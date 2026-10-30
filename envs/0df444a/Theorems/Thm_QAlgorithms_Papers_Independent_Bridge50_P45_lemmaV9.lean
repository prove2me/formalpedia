-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaV9
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaV9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:34:24.00237+00:00
-- url     : https://prove2.me/theorems/f19f167d-dfb8-416b-ad11-ab7efd1592e6
-- title:
--   The dummy-channel comparison for a shared code
-- statement:
--   Let $X$ be an arbitrary nonempty alphabet, let $H$ be a nonzero finite-dimensional complex Hilbert space, and let $W:X\to\mathcal S(H)$ be a classical-quantum channel. Write $\mathcal P_f(X)$ for the finitely supported probability laws. For the trace-normalized natural-log divergence $D^t_\alpha$ of the Petz, sandwiched ($*$), or log-Euclidean ($\flat$) family, define $\chi^t_{\alpha,1}(W,P)=\inf_\sigma D^t_\alpha(\mathbb W(P)\|P\otimes\sigma)$ and $\chi^t_{\alpha,2}(W,P)=\inf_\sigma\sum_xP(x)D^t_\alpha(W(x)\|\sigma)$, where both infima range over output density operators and $\mathbb W(P)=\sum_xP(x)|x\rangle\langle x|\otimes W(x)$. Define $\chi^t_\alpha(W)=\sup_{P\in\mathcal P_f(X)}\chi^t_{\alpha,1}(W,P)$, $R^t_\alpha(W)=\inf_\sigma\sup_xD^t_\alpha(W(x)\|\sigma)$, and $\chi(W,P)=\chi^t_{1,i}(W,P)$, $\chi(W)=\chi^t_1(W)$. These are distinct definitions before any asserted equalities.
--
--   Let $V$ be another cq channel on the same alphabet and output space. Let $n\ge1$, let $C_n=(\varphi_n,D_n)$ be a code with $M_n\ge1$ messages, and let $a\in\mathbb R$. Using exactly the same encoder and POVM for the two channels,
--   $$P_s(W^{\otimes n},C_n)\ge e^{-na}\left\{P_s(V^{\otimes n},C_n)-\frac1{M_n}\sum_{k=1}^{M_n}\operatorname{Tr}\left(V^{\otimes n}(\varphi_n(k))-e^{na}W^{\otimes n}(\varphi_n(k))\right)_+\right\}.$$
--   Here $A_+$ is the spectral positive part of a Hermitian operator; each trace has its own positive part. Code success is the uniform-message average. Repeated codewords and zero POVM effects are permitted.
--
--   This comparison transfers success from a dummy channel without truncating the full lower bound.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 29, Lemma V.9 Let W ∈ C(H|X ) be a classical-quantum channel. For any code Cn = (φn , Dn ), any

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

/-- Lemma V.9, PDF p.29 (115): the SAME encoder and decoder are used for W and V.
Positive parts are taken inside each trace; the outer lower bound is not truncated. -/
theorem lemmaV9 [Nonempty X] [Nonempty I] (W V : X → Mat I) (hW : CQ W) (hV : CQ V) (n : ℕ) (hn : 0 < n)
    (C : CQBlockCode X I n) (a : ℝ) :
    Real.exp (-(n : ℝ)*a) * (cqAverageSuccess V C - (C.messages : ℝ)⁻¹ *
      ∑ m, (cfc (fun x : ℝ => max 0 x)
        (memorylessOutputs V n (C.encoder m) -
          (Real.exp ((n : ℝ)*a) : ℂ) • memorylessOutputs W n (C.encoder m))).trace.re) ≤
      cqAverageSuccess W C := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
