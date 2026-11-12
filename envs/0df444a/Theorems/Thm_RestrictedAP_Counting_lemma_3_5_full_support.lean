-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_5_full_support
-- name    : RestrictedAP.Counting.lemma_3_5_full_support
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:16:45.690327+00:00
-- url     : https://prove2.me/theorems/1620f4f9-66fe-4e0c-8959-dfdc75cda547
-- title:
--   Lemma 3.5 for nu of full support (corrected: every letter of Sigma has probability at least alpha)
-- statement:
--   Source (Lemma 3.5, p. 17): for $\nu$ with atoms of probability at least $\alpha$ and a collection $\mathcal P$ of $r$ $M$-discrete product functions with $\mathrm{rk}(\mathcal P)\ge D$, for every $\vec b\in\prod_P\mathrm{Image}(P)$, $\big|\Pr_{x\sim\nu^{\otimes n}}[\forall P,\ P(x)=b_P]-\prod_P 1/\mathrm{ord}(P)\big|\le 2^{-\Omega_{M,r,\alpha}(D)}$.
--
--   Variant: the same bound under the hypothesis $\nu(a)\ge\alpha$ for **every** $a\in\Sigma$.
--
--   Difference: the atom bound is required on all of $\Sigma$; the proof applies Fact 2.12 (1), which needs it (finding I3).
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 17, Lemma 3.5 (corrected)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

namespace RestrictedAP.Counting

theorem lemma_3_5_full_support (M r : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ),
        IsDist ν → (∀ a, α ≤ ν a) → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        RankAtLeast PP (D : ℝ) →
        ∀ b : ((Fin n → Sig) → ℂ) → ℂ, (∀ P ∈ PP, b P ∈ Set.range P) →
          |(∑ x : Fin n → Sig, if (∀ P ∈ PP, P x = b P) then tensorPow ν n x else 0) -
              ∏ P ∈ PP, (1 / (orderOf P : ℝ))| ≤ (2 : ℝ) ^ (-(c * D)) := by sorry

end RestrictedAP.Counting
