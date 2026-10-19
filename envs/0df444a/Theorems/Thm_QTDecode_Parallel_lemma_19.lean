-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_19
-- name    : QTDecode.Parallel.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:07.783777+00:00
-- url     : https://prove2.me/theorems/ad3aef80-4134-40c2-91ae-5f3904f2d475
-- title:
--   Lemma 19, p. 29 — for |e| < 2⁻¹⁶ε³κ²δ²n/Δ, 1/2-sequential decoding never stalls and switching to ε still converges
-- statement:
--   Fix $\varepsilon\in(0,1/2)$ and $\delta,\kappa>0$. There is $\Delta_0$ such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs; let $C_A,C_B$ have minimum distance at least $\delta\Delta$ and let $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ be $\kappa$-product-expanding; let $n=|Q|$. Let $e$ be a $\sigma_x$-type error with
--   $$|e|\ <\ \frac1{2^{16}}\,\varepsilon^3\kappa^2\delta^2\,\frac n\Delta,$$
--   let $\varepsilon_v$ ($v\in V_1$) be any minimum-weight local corrections and $Z=\sum_{v\in V_1}\varepsilon_v$ the mismatch. Then for every run of $\ell\ge0$ steps of the sequential decoder of parameter $1/2$ (Algorithm 2) from $Z$:
--
--   1. if the current mismatch $\hat Z_\ell$ is non-zero, a further step of parameter $1/2$ is available, so sequential decoding with parameter $1/2$ terminates;
--   2. if the parameter is switched from $1/2$ to $\varepsilon$ at this stage, the sequential decoder of parameter $\varepsilon$ converges: every run of it from the current state that has not reached $\hat Z=0$ can be continued.
--
--   Since a parallel substep has the same effect as a sequence of steps of parameter $1/2$, this keeps the parallel decoder in a state where Lemma 18 applies.
--
--   **Formalization Note** "$\Delta$ large enough" is inherited from Theorem 12 and appears as $\exists\Delta_0$ depending on $\varepsilon,\delta,\kappa$. The reading of "terminate" follows the explanation after the statement on p. 29: from any stage, the sequence of increments can be extended until $\hat Z=0$; since every step strictly lowers $|\hat Z|$, never being stuck is the same as terminating.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 29, Lemma 19 and the explanation following it (proof p. 30)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 19, p. 29 (as explained after its statement, p. 29), with "`Δ` large enough" (inherited
from Theorem 12) made explicit. Let `ε ∈ (0, 1/2)`, `δ, κ > 0`. There is `Δ₀` such that for
`Δ ≥ Δ₀`, non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`, local codes `C_A`, `C_B` of minimum
distance at least `δΔ` with `κ`-product-expanding dual tensor code, a `σ_x`-type error with
`|e| < 2⁻¹⁶ ε³κ²δ² n/Δ` and any choice of minimum-weight local corrections `ε_v`, `v ∈ V₁`: after
any number `ℓ` of steps of the sequential decoder of parameter `1/2` from the mismatch `Z`,
1. if the current mismatch is non-zero, a further step of parameter `1/2` exists (sequential
   decoding with parameter `1/2` terminates);
2. the sequential decoder of parameter `ε` converges from the current state. -/
theorem lemma_19 :
    ∀ ε δ κ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
      A.card = Δ → B.card = Δ →
      (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) →
      IsRamanujanAdj (leftCayleyAdj A) Δ →
      (∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ)) →
      IsRamanujanAdj (rightCayleyAdj B) Δ →
      (∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) →
      ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
      HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
      IsProductExpanding CA CB Δ κ →
      ∀ e : G × A × B → ZMod 2,
      (hammingNorm e : ℝ) < 1 / 2 ^ 16 * ε ^ 3 * κ ^ 2 * δ ^ 2 *
          (Fintype.card (G × A × B) : ℝ) / Δ →
      ∀ εsel : G × (Bool × Bool) → A × B → ZMod 2,
      (∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → IsMinLocalCorrection CA CB e v (εsel v)) →
      ∀ (s : ℕ → SeqDecState (G × A × B)) (ℓ : ℕ),
        IsSeqDecRun CA CB (1 / 2) (qtMismatch εsel) s ℓ →
        ((s ℓ).Z ≠ 0 → ∃ s', SeqDecStep CA CB (1 / 2) (s ℓ) s') ∧
        SeqConverges CA CB ε (s ℓ) := by sorry

end QTDecode.Parallel
