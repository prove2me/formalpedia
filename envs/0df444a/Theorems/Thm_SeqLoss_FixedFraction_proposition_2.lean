-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_proposition_2
-- name    : SeqLoss.FixedFraction.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:07.901987+00:00
-- url     : https://prove2.me/theorems/a05eefa1-74e3-4f1f-8f72-21477f25822d
-- title:
--   Proposition 2, p. 12 — population monotonicity and merging proofness hold iff $\varphi(e_n)=\varphi^\lambda(e_n)$ for some $\lambda\in[0,1]$
-- statement:
--   A rule $\varphi$ satisfies population monotonicity and merging proofness if and only if there is $\lambda\in[0,1]$ such that, for each $n$,
--   $$\varphi(e_n)=\varphi^\lambda(e_n),$$
--   i.e. $\varphi(e_n)=(1-\lambda,0,\dots,0,\lambda)$ for $n\ge 2$ (and $\varphi(e_1)=(1)$).
--
--   Proposition 2 pins down a rule on the elementary problems; combined with Proposition 1 it yields Theorem 1.
--
--   **Formalization Note.** Population monotonicity is Axiom 3 with the corrected range $1\le j<n$; with the printed range $1<j<n$ the proposition is false (counterexample in the Axioms item). The parameter $\lambda\in[0,1]$ is part of the conclusion.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, p. 12, §3.3, Proposition 2; proof Appendix A, pp. 22–23

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem proposition_2 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (PopulationMonotone φ ∧ MergingProof φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1, ∀ n : ℕ, φ n (elem n) = fixedFraction lam n (elem n) := by sorry

end SeqLoss.FixedFraction
