-- Prove2me | Theorems.Thm_RestrictedAP_Counting_fact_2_12_full_support
-- name    : RestrictedAP.Counting.fact_2_12_full_support
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:15:10.654772+00:00
-- url     : https://prove2.me/theorems/a9b8e066-9e1e-4505-bc03-29c7584b6de7
-- title:
--   Fact 2.12 for nu of full support (corrected: every letter of Sigma has probability at least alpha)
-- statement:
--   Source (Fact 2.12, p. 9): if $P:\Sigma^n\to\mathbb D$ is an $M$-discrete product function, $\nu$ a distribution on $\Sigma$ in which each atom has probability at least $\alpha$, and $\Delta_{\mathrm{symbolic}}(P,1)\ge D$, then $|\mathbb E_{\nu^{\otimes n}}P|\le 2^{-\Omega_{\alpha,M}(D)}$ and $\|T^{\otimes n}_{1-\tau}P\|_2\le 2^{-\Omega_{\alpha,\tau,M}(D)}$ for all $\tau>0$.
--
--   Variant: the same two bounds, with the hypothesis that $\nu(a)\ge\alpha$ for **every** $a\in\Sigma$ (so $\nu$ has full support), constants quantified before the instance as in the mission item.
--
--   Difference: the atom bound is required on all of $\Sigma$, not only on the support of $\nu$; the proof on p. 10 uses it for arbitrary letters $a,b$.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 9, Fact 2.12 (corrected)

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators

namespace RestrictedAP.Counting

theorem fact_2_12_full_support :
    (∀ (M : ℕ) (α : ℝ), 0 < α → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → (∀ a, α ≤ ν a) → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        ‖expectC (tensorPow ν n) P‖ ≤ (2 : ℝ) ^ (-(c * D))) ∧
    (∀ (M : ℕ) (α τ : ℝ), 0 < α → 0 < τ → τ ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → (∀ a, α ≤ ν a) → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        l2Norm (tensorPow ν n) (noiseOp ν (1 - τ) n P) ≤ (2 : ℝ) ^ (-(c * D))) := by sorry

end RestrictedAP.Counting
