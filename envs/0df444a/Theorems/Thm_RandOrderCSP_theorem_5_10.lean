-- Prove2me | Theorems.Thm_RandOrderCSP_theorem_5_10
-- name    : RandOrderCSP.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:22.58661+00:00
-- url     : https://prove2.me/theorems/1655bb8c-c3bd-4be1-9575-426dc1ed51de
-- title:
--   Theorem 5.10 — the inductive step
-- statement:
--   For all integers $k,q\ge2$ and every $k$-uniform $\Delta_1(\mathbb Z_q^k)$-colored gadget hypergraph $\Phi_*=(G_*,\mathcal Y_*)$, there are $\alpha_0>0$ and $\zeta_0\ge1$ such that for every $\zeta\ge\zeta_0$ and $\delta\in(0,1/2)$ there are $\sigma\in(0,1)$ and $\zeta''\ge1$ with the following property. For every $\alpha\in(0,\alpha_0]$, all $n,b,b',s\ge1$ with
--
--   $$2\log_q(2/\delta)\le s\le\sigma n,\qquad b+b'+\log_q\frac1{1-\delta}\le s,$$
--
--   and every $(\zeta,s,b)$-bounded distribution $D$ on $\mathbb Z_q^{\mathcal V_{G_*^n}}$, for $\Phi=(H,\mathcal Y)\sim\mathrm{Poi}(\Phi_*^n,\alpha n^{-(k-1)})$ the event
--
--   "$\mathrm{Acy}(H)$ and there is a nontrivial $\mathcal B\subseteq\mathbb Z_q^{\mathcal E_H\times[k]}$ with $\log_q|\mathcal B|\ge km_H-b'$ such that $\mathrm{Post}(D,\Phi,\mathcal B)$ is not $(\zeta'',s,b+b'+\log_q\frac1{1-\delta})$-bounded"
--
--   has probability at most $5\delta$.
--
--   A short message therefore rarely destroys boundedness of the posterior, which is what lets the hybrid argument continue through the rounds.
--
--   Differences from the source:
--   - encoding: (ζ, s, b)-bounded, with the envelope defined assuming s ≤ (e²q⁴/ζ²)N → that inequality is a conjunct of the predicate, also under the negation; reason: σ is chosen after ζ″, so s ≤ σn secures the inequality for ζ″
--   - encoding: log_q‖μ_D‖_∞ ≤ b → |μ_D(X)| ≤ q^b for all X; reason: equivalent for a distribution, whose density has sup norm at least 1
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 5.10, p.24

import Mathlib
import Definitions.Def_RandOrderCSP_IsOneWiseUniform
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw
import Definitions.Def_RandOrderCSP_obsKernel
import Definitions.Def_RandOrderCSP_envelope

namespace RandOrderCSP

/-- **Theorem 5.10 (inductive step).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating
CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 5.10, p.24.

**Formalization Note.** `ℬ` ranges over all subsets of the finite label set; `m_H = ∑_e c(e)`.
`IsEnvBoundedB` carries the conjunct `s ≤ (e²q⁴/ζ²)N` of the envelope's domain. In the event it is
negated with `ζ″`, and the order of quantifiers (`σ` after `ζ″`) lets `s ≤ σn` secure that conjunct. -/
theorem theorem_5_10 {k q : ℕ} [NeZero q] (hk : 2 ≤ k) (hq : 2 ≤ q) {V E : Type} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype E] [DecidableEq E] (G : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (hY : ∀ j, IsOneWiseUniform (Y j)) :
    ∃ α₀ ζ₀ : ℝ, 0 < α₀ ∧ 1 ≤ ζ₀ ∧
      ∀ ζ : ℝ, ζ₀ ≤ ζ → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ σ ζ'' : ℝ, 0 < σ ∧ σ < 1 ∧ 1 ≤ ζ'' ∧
          ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ n b b' s : ℕ, 1 ≤ n → 1 ≤ b → 1 ≤ b' → 1 ≤ s →
            2 * Real.logb q (2 / δ) ≤ s → (s : ℝ) ≤ σ * n →
            (b : ℝ) + b' + Real.logb q (1 / (1 - δ)) ≤ s →
            ∀ D : (V × Fin n → ZMod q) → ℝ, IsDistr D → IsEnvBoundedB ζ s (b : ℝ) D →
              poiLaw (E × (Fin k → Fin n)) (poiRate α n k)
                {c | (sparsify (blowup G n) c).Acy ∧
                  ∃ B : Finset ((Σ e, Fin (c e)) × Fin k → ZMod q),
                    0 < pushObsMass (sparsify (blowup G n) c)
                      (sparsifyColor (blowupColor Y n) c) D B ∧
                    (k : ℝ) * ((∑ e, c e : ℕ) : ℝ) - b' ≤ Real.logb q (B.card : ℝ) ∧
                    ¬ IsEnvBoundedB ζ'' s ((b : ℝ) + b' + Real.logb q (1 / (1 - δ)))
                      (posterior (sparsify (blowup G n) c)
                        (sparsifyColor (blowupColor Y n) c) D B)} ≤
                ENNReal.ofReal (5 * δ) := by sorry

end RandOrderCSP
