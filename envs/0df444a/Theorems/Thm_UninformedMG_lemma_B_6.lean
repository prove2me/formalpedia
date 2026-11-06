-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_6
-- name    : UninformedMG.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:31.591027+00:00
-- url     : https://prove2.me/theorems/b830d274-7b87-4b61-9345-4399f880c313
-- title:
--   Lemma B.6 (first claim) — $\min_{q\in\mathcal Q(z)}\Phi(z,q)\le 2S(A+1)\lambda$, attained
-- statement:
--   Let $\bar{\mathcal J}_h(z,s,q)$ be the bandit cost (22) and $\Phi(z,q)=\sup_{T\in\mathcal T_{\mathrm{all}}}\{\mathrm{Drift}(z,q,T)+\lambda\sum_{h,s}d^{z,q,T}_h(s)\bar{\mathcal J}_h(z,s,q)\}$, on the grid $\mathcal V$ of Eq. (19), with $|A_h|\le A$ for every step. For any $0<\lambda\le1/(2S)$, any $z\in\mathcal Z$ and any initial state $s_1$, the minimum of $\Phi(z,\cdot)$ over $\mathcal Q(z)$ is attained, and
--   $$\min_{q\in\mathcal Q(z)}\Phi(z,q)\le2S(A+1)\lambda.$$
--
--   The attainment makes the argmin in step (23) of Algorithm 1 nonempty, and the bound is the drift–cost term of the regret analysis. This item is the first sentence of Lemma B.6. Its second sentence, the running time $O(S^2KN^{7/2}\log(KS))$ of computing the $q^k$, is not posed: it needs a cost model for conic solvers, and the proof of Theorem 2.1 does not use it.
--
--   Differences from the source:
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - reading: min_{q∈𝒬(z)} Φ(z,q) ≤ 2S(A+1)λ → the minimum is attained by some q ∈ 𝒬(z), and its value is ≤ 2S(A+1)λ; reason: "min" read literally; attainment holds since 𝒬(z) is compact and Φ(z,·) lower semicontinuous (p.24)
--   - encoding: Φ for the initial state of the episode → Φ for every initial state s₁ (explicit argument); reason: Φ depends on s₁ through d; same statement for each s₁
--   - encoding: z ∈ 𝒵 → the pair (w, π) of Eq. (4); reason: every z ∈ 𝒵 is w·π and every quantity used is unchanged by π at w(v) = 0
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.6 (first sentence), p.23 (PDF p.25), proof pp.23–24

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Phi

namespace UninformedMG

/-- **Lemma B.6 (Drift bound with bandit feedback), first claim** (p.23 = PDF p.25; proof to p.24).
Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

Let `J̄_h(z,s,q)` be as in Eq. (22) and `Φ(z,q) = sup_{T∈T_all} {Drift(z,q,T) + λ∑_{h,s} d_h(s) J̄_h(z,s,q)}`.
For any `0 < λ ≤ 1/(2S)` and `z ∈ Z`, `min_{q∈Q(z)} Φ(z, q) ≤ 2S(A+1)λ`.

**Formalization Note.** On the grid `V` of Eq. (19), for every initial state `s₁`: the minimum over
`Q(z)` is attained (by some `q`), and its value is at most `2S(A+1)λ`. `A` is any bound on `|A_h|`.
The running-time sentence of the lemma is not formalized. -/
theorem lemma_B_6 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (w : (grid G K).C → ℝ) (π : CPolicy (grid G K)) (hz : IsJoint (grid G K) w π) (s₁ : G.St 0) :
    ∃ q : Mixing (grid G K), feasibleMix (grid G K) lam w q ∧
      (∀ q', feasibleMix (grid G K) lam w q' → Phi (grid G K) lam w π q s₁ ≤ Phi (grid G K) lam w π q' s₁) ∧
      Phi (grid G K) lam w π q s₁ ≤ 2 * (G.numStates : ℝ) * ((A : ℝ) + 1) * lam := by sorry

end UninformedMG
