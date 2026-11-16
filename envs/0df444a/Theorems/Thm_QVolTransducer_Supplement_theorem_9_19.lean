-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_9_19
-- name    : QVolTransducer.Supplement.theorem_9_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:46:21.859851+00:00
-- url     : https://prove2.me/theorems/c6acf964-69dd-4b4c-8da8-32292b9d54b3
-- title:
--   Theorem 9.19 — a transducer maps $|0\rangle$ to a state $\nu$-close to the uniform superposition over $K_{\zeta/\gamma}$ with complexity $\tilde O(dR+d^2)$
-- statement:
--   Let $3\le d\in\mathbb N$, $R\ge1$, $\nu>0$, $\gamma=1-1/(2d)$, and let $B_d\subseteq K\subseteq RB_d$ be a convex body accessible through membership oracles on grids with sufficiently small spacing $\zeta=\zeta(d,R,\nu)>0$. The bidirectional canonical transducer $C$ of Algorithm 1 acts as
--
--   $$|0\rangle\overset{C}{\rightsquigarrow}|\tilde\pi_{0,r_\ell,\zeta/\gamma}\rangle,\qquad\Big\||\tilde\pi_{0,r_\ell,\zeta/\gamma}\rangle-\frac1{\sqrt{|K_{\zeta/\gamma}|}}\sum_{x\in K_{\zeta/\gamma}}|x\rangle\Big\|\le\nu,$$
--
--   with transduction complexity $\tilde O(dR+d^2)$.
--
--   This is the quantum analogue of uniform sampling from a convex body, obtained by annealing from a concentrated Gaussian to the uniform distribution with amortized quantum walks.
--
--   **Formalization Note** Stated existentially: there are universal $c,k$ and, for small enough $\zeta$, one transducer $C$ (querying $O_{K,\zeta}$ and $O_{K,\zeta/\gamma}$) and a basis state $|0\rangle$ of its public space, both chosen before $K$, such that for every such $K$ the output is the state of a probability distribution on $K_{\zeta/\gamma}$ that is $\nu$-close to the uniform superposition, with complexity at most $c(dR+d^2)(\log(2+d)\log(2+R)\log(2+1/\nu))^k$.
--
--   Differences from the source:
--   - reading: the bidirectional canonical transducer in Algorithm 1 and its output |π̃_{0,r_ℓ,ζ/γ}⟩ → ∃ one bidirectional canonical transducer C and a basis state |0⟩ of its public space, chosen before K, whose output is the state of a probability distribution on K_{ζ/γ}; reason: the name π̃_{0,r_ℓ,ζ/γ} is internal to Algorithm 1; the theorem's content is the ν-closeness and the complexity (SUPPLEMENT.md decision 3, as the published goal reads Algorithm 2)
--   - reading: Õ(·) / O(· polylog) → universal c > 0 and k ∈ ℕ with a factor (log(2+d)·log(2+R)·log(2+1/ν))^k; reason: §2.1's Õ with log(2+·) so the factors are ≥ log 2 > 0 for every parameter value (base decisions 3–4)
--   - reading: a sufficiently small choice of ζ = ζ(d, R, ν) → ∃ ζ₀ > 0 depending only on d, R, ν, ∀ ζ ∈ (0, ζ₀], uniformly over K; reason: base decision 5
--   - encoding: states in ℂ^{K_{ζ/γ}} → the published gridState in ℂ^{(RB_d)_{ζ/γ}} (zero extension), the public space carrying a further K-independent summand; reason: the conventions of p.53 and of the published Theorem 9.16
--   - encoding: convex body B_d ⊆ K ⊆ RB_d → IsCompact K, Convex ℝ K, closedBall 0 1 ⊆ K ⊆ closedBall 0 R in EuclideanSpace ℝ (Fin d); reason: a convex body is a compact convex set; d ∈ ℕ = {1, 2, …} gives 1 ≤ d
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.19, p.65 (PDF p.67)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QVolTransducer_BiCanonical
import Definitions.Def_QVolTransducer_rejStat

namespace QVolTransducer.Supplement

open QAlgorithms

open Classical in
/-- **Uniform sampling from a convex body with a transducer** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 9.19, p.65 (PDF p.67); Algorithm 1,
p.65).

There are universal constants `c > 0` and `k ∈ ℕ` such that for all `3 ≤ d ∈ ℕ`, `R ≥ 1` and
`ν > 0` there is `ζ₀ = ζ₀(d, R, ν) > 0` with the following property. For every `0 < ζ ≤ ζ₀`,
with `γ = 1 − 1/(2d)`, there is one bidirectional canonical transducer `C`, querying the membership
oracles `O_{K,ζ}` and `O_{K,ζ/γ}`, and a fixed basis state `|0⟩` of its public space, such that for
every convex body `B_d ⊆ K ⊆ RB_d`: `|0⟩ ⇝_C |π̃⟩` with transduction complexity at most
`c (dR + d²) (log(2+d) log(2+R) log(2+1/ν))^k`, where `|π̃⟩` is the quantum state of a probability
distribution on `K_{ζ/γ}` with
`‖|π̃⟩ − (1/√|K_{ζ/γ}|) Σ_{x∈K_{ζ/γ}} |x⟩‖ ≤ ν`.

**Formalization Note** "The bidirectional canonical transducer in Algorithm 1" is stated
existentially (as the published goal reads Algorithm 2): the theorem's content about the output
`|π̃_{0,r_ℓ,ζ/γ}⟩` (a name internal to Algorithm 1) is that it is the state of a distribution on
`K_{ζ/γ}` that is `ν`-close to the uniform superposition. States live in `ℂ^{(RB_d)_{ζ/γ}}` (the
published `Grid`, zero extension, p.53), the public space carries a further `K`-independent summand
`ℂ^e`, and `|0⟩` is a basis vector `ket i₀` of the public space chosen before `K`. `Õ(dR + d²)` is
read as universal `c`, `k` with `log(2+·)` factors in `d`, `R`, `1/ν`; "sufficiently small
`ζ = ζ(d, R, ν)`" is `∃ ζ₀ > 0, ∀ ζ ∈ (0, ζ₀]`. `ν > 0` is not restricted (Algorithm 1's input
range `ν < 1/4` is not a hypothesis of the theorem). -/
theorem theorem_9_19 :
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, ∀ (d : ℕ) (R ν : ℝ), ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
      (3 ≤ d → 1 ≤ R → 0 < ν →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
        ∃ (e n : ℕ) (C : BiCanonical (Grid d (ζ / shrink d) R ⊕ Fin e)
            (Grid d ζ R ⊕ Grid d (ζ / shrink d) R) (Fin n))
          (i₀ : Grid d (ζ / shrink d) R ⊕ Fin e),
          ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
            Metric.closedBall 0 1 ⊆ K → K ⊆ Metric.closedBall 0 R →
            ∃ pK : (Fin d → ℤ) → ℝ,
              (∀ z, 0 ≤ pK z) ∧
              (∀ z, latticePt (ζ / shrink d) z ∉ K → pK z = 0) ∧
              ∑ z ∈ gridIdx d (ζ / shrink d) R, pK z = 1 ∧
              TransducesWithin (C.apply (twoGridOracle K ζ (ζ / shrink d) R)) (ket i₀)
                (embL (gridState pK))
                (c * (d * R + (d : ℝ) ^ 2) *
                  (Real.log (2 + d) * Real.log (2 + R) * Real.log (2 + 1 / ν)) ^ k) ∧
              ‖(gridState pK : EuclideanSpace ℂ (Grid d (ζ / shrink d) R)) -
                  gridState (fun z => if latticePt (ζ / shrink d) z ∈ K then
                    1 / (((gridIdx d (ζ / shrink d) R).filter
                      (fun y => latticePt (ζ / shrink d) y ∈ K)).card : ℝ) else 0)‖ ≤ ν) := by sorry

end QVolTransducer.Supplement
