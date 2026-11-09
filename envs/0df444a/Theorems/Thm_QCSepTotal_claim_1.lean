-- Prove2me | Theorems.Thm_QCSepTotal_claim_1
-- name    : QCSepTotal.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:17.003589+00:00
-- url     : https://prove2.me/theorems/1bbc7e48-bf02-4609-a7ae-02b8b4999be7
-- title:
--   Claim 1 — $\hat u,\hat v,\hat u',\hat v'$ with $g(\hat u+\hat v)=g(\hat u'+\hat v')\neq g(\hat u'+\hat v)$ and $\Delta\le2\tau$
-- statement:
--   Let $b\ge0$, let $g:\mathbb F_2^b\to\{0,1\}$ take both values, let $Q^{\hat u,\hat v}$ ($\hat u,\hat v\in\mathbb F_2^b$) and $Q_0$ be distributions on a common space, and let $\tau$ be real. Suppose (9) holds in the form
--   $$\Pr_{\hat u,\hat v\leftarrow U_b}\Bigl[\Delta\bigl(Q^{\hat u,\hat v},Q_0\bigr)>\tau\Bigr]<10^{-6}.$$
--   Then there exist $\hat u,\hat v,\hat u',\hat v'\in\mathbb F_2^b$ such that
--   $$g(\hat u+\hat v)=g(\hat u'+\hat v')\neq g(\hat u'+\hat v)\quad\text{and}\quad \Delta\bigl(Q^{\hat u,\hat v},Q^{\hat u',\hat v'}\bigr)\le2\tau .$$
--
--   In the proof of Theorem 4.1 it is applied with $g(p)=V(x,y;p)$, $Q^{\hat u,\hat v}=Q^{\hat u,\hat v}_{x,y}$ and $Q_0=Q_{x,y}$ for the pair given by Lemma 4.2; with Fact 1 and (1) it yields the final contradiction.
--
--   Differences from the source:
--   - generalization: g(p) = V(x, y; p), Q^{û,v̂}_{x,y} and Q_{x,y} for the pair of Lemma 4.2, τ = 6·10⁻⁵ → any g taking both values, any family Q^{û,v̂}, any Q₀ and any τ satisfying (9); reason: the proof uses only that g takes both values and (9)
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Claim 1, p.9; proved pp.9–10

import Mathlib
import Definitions.Def_QCSepTotal_tv

namespace QCSepTotal

/-- **Claim 1** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.9; proved pp.9–10). There exist
`û, v̂, û′, v̂′ ∈ F₂^b` such that `g(û + v̂) = g(û′ + v̂′) ≠ g(û′ + v̂)` and
`Δ(Q^{û,v̂}_{x,y}, Q^{û′,v̂′}_{x,y}) ≤ 2τ`.

**Formalization Note.** Stated for what its proof uses: any `g : F₂^b → {0,1}` taking both
values (the paper's `g(p) = V(x, y; p)` at a pair with `D_c(x, y) = 1`), any family of
distributions `Q^{û,v̂}` and any distribution `Q₀` (the paper's `Q_{x,y}`) satisfying (9):
the fraction of pairs `(û, v̂)` with `Δ(Q^{û,v̂}, Q₀) > τ` is less than `10⁻⁶`. -/
theorem claim_1 {T : Type*} (b : ℕ) (g : (Fin b → ZMod 2) → Bool) (hg : ∃ p p', g p ≠ g p')
    (Q : (Fin b → ZMod 2) → (Fin b → ZMod 2) → PMF T) (Q₀ : PMF T) (τ : ℝ)
    (h9 : ((Finset.univ.filter fun uv : (Fin b → ZMod 2) × (Fin b → ZMod 2) =>
        τ < tv (Q uv.1 uv.2) Q₀).card : ℝ) / 2 ^ (2 * b) < 1 / 10 ^ 6) :
    ∃ u v u' v' : Fin b → ZMod 2, g (u + v) = g (u' + v') ∧ g (u' + v') ≠ g (u' + v) ∧
      tv (Q u v) (Q u' v') ≤ 2 * τ := by sorry

end QCSepTotal
