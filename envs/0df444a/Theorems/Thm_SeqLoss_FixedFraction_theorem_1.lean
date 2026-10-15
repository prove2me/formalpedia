-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_theorem_1
-- name    : SeqLoss.FixedFraction.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:04.656892+00:00
-- url     : https://prove2.me/theorems/9562a2e7-9390-4589-a888-8295686f840c
-- title:
--   Theorem 1, p. 12 — additivity, zero truncation, merging proofness and population monotonicity characterize the fixed-fraction rules
-- statement:
--   Let $\varphi$ be a (continuous) rule for sequentially triggered losses. Then $\varphi$ satisfies
--
--   1. additivity: $\varphi(\ell)+\varphi(\ell')=\varphi(\ell+\ell')$,
--   2. zero truncation: $\varphi_i(\ell)=\varphi_i(\ell,0)$,
--   3. merging proofness: $\varphi_i(e_3)+\varphi_{i+1}(e_3)\le\varphi_i(e_2)$ for $i=1,2$, and
--   4. population monotonicity: $\varphi_i(e_n)\ge\varphi_i(e_{n+1})$ and $\varphi_k(e_n)\ge\varphi_{k+1}(e_{n+1})$ for $1\le i\le j<k\le n$, $1\le j<n$,
--
--   if and only if there is $\lambda\in[0,1]$ such that $\varphi=\varphi^\lambda$, that is, for every $n$ and every loss vector $\ell\in L^n$,
--   $$\varphi_1(\ell)=\lambda\ell_1+(1-\lambda)L,\qquad \varphi_i(\ell)=\lambda\ell_i\quad(i=2,\dots,n).$$
--
--   This is the paper's main characterization: the four normative requirements leave exactly a one-parameter family of compromises between the direct liability rule ($\lambda=1$) and the indirect liability rule ($\lambda=0$).
--
--   **Formalization Note.** "$\varphi=\varphi^\lambda$" is stated as agreement on every loss vector $\ell\ge 0$ for every $n$; a rule's values outside $L^n$ are meaningless. Population monotonicity is Axiom 3 with the corrected range $1\le j<n$: with the printed $1<j<n$ the theorem is false (counterexample in the Axioms item). $\lambda\in[0,1]$ is part of the conclusion.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, p. 12, §3.3, Theorem 1

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem theorem_1 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ) :
    (Additive φ ∧ ZeroTruncation φ ∧ MergingProof φ ∧ PopulationMonotone φ) ↔
    ∃ lam ∈ Set.Icc (0:ℝ) 1,
      ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ → φ n ℓ = fixedFraction lam n ℓ := by sorry

end SeqLoss.FixedFraction
