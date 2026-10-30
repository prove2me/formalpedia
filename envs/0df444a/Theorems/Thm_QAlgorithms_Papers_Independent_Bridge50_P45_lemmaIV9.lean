-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaIV9
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaIV9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:28:52.827123+00:00
-- url     : https://prove2.me/theorems/5ae6b6ed-5d3c-4b2e-bd5e-848be7d79be6
-- title:
--   Symmetric minimizing references for general symmetric laws
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   For each blocklength $n$, choose a universal symmetric state $\sigma_{u,n}$ as in Lemma II.8: it is permutation invariant and central in the invariant algebra, dominates every symmetric density operator by a factor $v_{n,d}$, and has at most $v_{n,d}$ distinct eigenvalues, where $d=\dim H$ and $v_{n,d}\le(n+1)^{(d+2)(d-1)/2}$. Write $\mathcal E_n$ for pinching by this state.
--
--   Let $P_n$ be any symmetric probability mass function on $X^n$, including countably supported laws of infinite support. For $\alpha>1$ and $t\in\{*,\flat\}$, or for $t=\{\}$ and $1<\alpha\le2$, both minimizations satisfy
--   $$\chi^t_{\alpha,1}(\mathcal E_nW^{\otimes n},P_n)
--   =\min_{\sigma_n\in\mathcal S_{\rm sym}(H^{\otimes n})}
--   D^t_\alpha((\mathcal E_n\mathbb W^{\otimes n})(P_n)\|P_n\otimes\sigma_n),$$
--   $$\chi^t_{\alpha,2}(\mathcal E_nW^{\otimes n},P_n)
--   =\min_{\sigma_n\in\mathcal S_{\rm sym}(H^{\otimes n})}
--   \sum_xP_n(x)D^t_\alpha(\mathcal E_nW^{\otimes n}(x)\|\sigma_n).$$
--   Both minima are attained, and they equal the corresponding infima over invertible symmetric density operators. The first objective is represented by its nonnegative block sum $\frac1{\alpha-1}\log\sum_xP_n(x)Q^t_\alpha(\mathcal E_nW^{\otimes n}(x)\|\sigma_n)$, so no finite classical register is imposed.
--
--   This preserves the general-law regime of the source rather than silently requiring finite support.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 23, Lemma IV.9 Let Pn ∈ P(X n ) be a symmetric probability density on X n . Then for any α > 1 and

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Nonempty X] [Nonempty I]

/-- Lemma IV.9, PDF pp.23-25 (96)-(97). General symmetric mass functions are
allowed, with countably infinite support. Both constrained minima are attained,
and strictly positive symmetric references give the same infimum. -/
theorem lemmaIV9 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : CQ W) (n : ℕ) (U : Universal I n)
    (p : (Fin n → X) → ℝ) (hp : MassLaw p) (hsym : SymmetricLaw p)
    (t : Flavor) (a : ℝ) (ha : 1 < a) (ht : t = .b ∨ t = .star ∨ (t = .petz ∧ a ≤ 2))
    (i : Fin 2) :
    (∃ sigma : Mat (Fin n → I), IsDensityMatrix sigma ∧ TensorPermutationInvariant sigma ∧
      massInformation t a i (pinchedChannel W n U) p =
        massObjective t a i (pinchedChannel W n U) p sigma ∧
      ∀ A : Mat (Fin n → I), IsDensityMatrix A → TensorPermutationInvariant A →
        massObjective t a i (pinchedChannel W n U) p sigma ≤
          massObjective t a i (pinchedChannel W n U) p A) ∧
    massInformation t a i (pinchedChannel W n U) p =
      ⨅ sigma : {A : Mat (Fin n → I) // IsDensityMatrix A ∧ TensorPermutationInvariant A ∧ A.PosDef},
        massObjective t a i (pinchedChannel W n U) p sigma.1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
