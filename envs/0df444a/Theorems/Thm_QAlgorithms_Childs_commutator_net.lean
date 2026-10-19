-- Prove2me | Theorems.Thm_QAlgorithms_Childs_commutator_net
-- name    : QAlgorithms.Childs.commutator_net
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:31:45.65083+00:00
-- url     : https://prove2.me/theorems/74529e0a-b999-4d91-b3c7-7f3f0b0ff3b0
-- title:
--   Group commutators of an ϵ²-net of S_ϵ form an O(ϵ³)-net of S_{ϵ²}
-- statement:
--   For $U,V\in SU(2)$ write $[\![U,V]\!]=UVU^{-1}V^{-1}$ for the group commutator. For $\epsilon\ge0$ let
--
--   $$
--   S_\epsilon=\{U\in SU(2):\|I-U\|\le\epsilon\}
--   $$
--
--   be the $\epsilon$-ball around the identity, with $\|\cdot\|$ the spectral norm. For $\Gamma,S\subseteq SU(2)$, $\Gamma$ is a $\delta$-net for $S$ if every $A\in S$ has some $U\in\Gamma$ with $\|A-U\|\le\delta$.
--
--   The lemma says there are constants $C>0$ and $\epsilon_0>0$ such that, for every $0<\epsilon\le\epsilon_0$ and every $\Gamma\subseteq SU(2)$, the following holds. If $\Gamma$ is an $\epsilon^2$-net for $S_\epsilon$, then
--
--   $$
--   [\![\Gamma,\Gamma]\!]=\{[\![U,V]\!]:U,V\in\Gamma\}\ \text{is a } C\epsilon^3\text{-net for } S_{\epsilon^2}.
--   $$
--
--   This is the key step of the Solovay–Kitaev construction. Applied recursively, it turns a coarse net near the identity into nets of doubly-exponentially improving precision.
--
--   **Formalization Note** The source writes $O(\epsilon^3)$ as $\epsilon\to0$. Here it is written as explicit constants $C$ and $\epsilon_0$, chosen before $\Gamma$, because the source's recursion uses one constant at every level.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 16, Lemma 2.3. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false

namespace QAlgorithms.Childs

open QAlgorithms



/-- Childs, Lemma 2.3, PDF p. 16. If `Γ ⊆ SU(2)` is an `ϵ²`-net for `S_ϵ = {U ∈ SU(2) :
‖I − U‖ ≤ ϵ}`, then `⟦Γ, Γ⟧ = {U V U⁻¹ V⁻¹ : U, V ∈ Γ}` is an `O(ϵ³)`-net for `S_{ϵ²}`.
The `O(ϵ³)` is with respect to `ϵ → 0` (PDF p. 17), with a constant independent of `Γ` (the
recursion on p. 16 uses one constant `k` at every level): there are `C > 0` and `ϵ₀ > 0` such
that for every `0 < ϵ ≤ ϵ₀` and every such `Γ`, `⟦Γ, Γ⟧` is a `C ϵ³`-net for `S_{ϵ²}`. -/
theorem commutator_net :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ Γ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ),
        IsNet Γ (su2Ball ε) (ε ^ 2) → IsNet (commutatorSet Γ) (su2Ball (ε ^ 2)) (C * ε ^ 3) := by
  sorry

end QAlgorithms.Childs
