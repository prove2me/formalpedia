-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_endpoints_elem
-- name    : SeqLoss.FixedFraction.endpoints_elem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:00.701807+00:00
-- url     : https://prove2.me/theorems/0d7c36c1-342e-4ed7-b754-dd3de3f27be5
-- title:
--   Proof of Proposition 2, p. 23 — $\varphi_1(e_n)=\varphi_1(e_2)$ and $\varphi_n(e_n)=\varphi_2(e_2)$
-- statement:
--   Let $\varphi$ be a rule satisfying population monotonicity and merging proofness. Then for each $n\ge 2$ the initiator and the last agent of $e_n$ carry exactly their liabilities in $e_2=(0,1)$:
--   $$\varphi_1(e_n)=\varphi_1(e_2),\qquad \varphi_n(e_n)=\varphi_2(e_2).$$
--
--   With $\varphi(e_2)=(1-\lambda,\lambda)$ and the vanishing of intermediate agents, this gives $\varphi(e_n)=\varphi^\lambda(e_n)$.
--
--   **Formalization Note.** 0-based: the initiator is index $0$ and the last agent of $e_n$ is index $n-1$. Population monotonicity is Axiom 3 with the corrected range $1\le j<n$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix A, p. 23, proof of Proposition 2, (⟹), last paragraph

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem endpoints_elem (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (hn : 2 ≤ n) :
    φ n (elem n) ⟨0, by omega⟩ = φ 2 (elem 2) 0 ∧
    φ n (elem n) ⟨n - 1, by omega⟩ = φ 2 (elem 2) 1 := by sorry

end SeqLoss.FixedFraction
