-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_exponentialTransfer
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.exponentialTransfer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:52:32.613961+00:00
-- url     : https://prove2.me/theorems/caf30ca4-5540-41d8-8fc8-25af3cee5544
-- title:
--   Section VII: exponential strong-converse transfer
-- statement:
--   Let $\mathcal N$ be a finite type-I degradable channel, and let $\mathcal M$ be the associated symmetric channel constructed from its fixed dilations and a normalized test vector of full input Schmidt rank as in Lemma 18. Let $f:[0,\infty)\to\mathbb R$ be continuous and nondecreasing, with $f(0)=0$. Suppose one such function bounds every $c>0$ by
--
--   $$
--   \limsup_{n\to\infty}\frac1n\log_2 N_E(n,1-2^{-cn}\mid\mathcal M)\le f(c).
--   $$
--
--   Then there is a continuous nondecreasing $g:[0,\infty)\to\mathbb R$, with $g(0)=0$, chosen before $c$, such that for every $c>0$,
--
--   $$
--   \limsup_{n\to\infty}\frac1n\log_2 N_E(n,1-2^{-cn}\mid\mathcal N)\le Q^{(1)}(\mathcal N)+g(c).
--   $$
--
--   The errors are purified-distance errors of entanglement generation. This transfers an exponential strong-converse profile conditionally, without asserting that the companion channel already has one.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 12, Section VII: exponential strong-converse transfer

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Section VII exponential-transfer Remark, PDF p.12: a single continuous
nondecreasing profile controls every c>0. The output profile precedes c too. -/
theorem exponentialTransfer [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (negative : Bool) (hfactor : IsTypeIFactorization U V negative)
    (phi0 : EuclideanSpace ℂ (A × A)) (hphi0 : ‖phi0‖ = 1)
    (hfull : (traceRight (pureDensity phi0)).det ≠ 0)
    (W : Matrix (E × E) (Fin (supportDimension U V phi0)) ℂ)
    (hW : P67.IsIsometry W) (hassoc : Associated U V phi0 W)
    (hswap : P67.environmentSwap * W = swapSign negative • W)
    (f : ℝ → ℝ) (hf : ExponentProfile f)
    (hbound : ∀ c : ℝ, 0 < c → limsup (exponentialRate W c) atTop ≤ f c) :
    ∃ g : ℝ → ℝ, ExponentProfile g ∧ ∀ c : ℝ, 0 < c →
      limsup (exponentialRate U c) atTop ≤ P67.maximumCoherentInformation U + g c := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
