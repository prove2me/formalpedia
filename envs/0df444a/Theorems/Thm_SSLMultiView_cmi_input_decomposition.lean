-- Prove2me | Theorems.Thm_SSLMultiView_cmi_input_decomposition
-- name    : SSLMultiView.cmi_input_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T18:29:07.137067+00:00
-- url     : https://prove2.me/theorems/2947035e-e453-4cc1-8339-238e881ce787
-- title:
--   Theorem 2 (proof, first display): $I(Z_X;X|T)=I(Z_X;S|T)+I(Z_X;X|S,T)$
-- statement:
--   Let $(X,S,T)$ have a joint probability mass function on finite sets, and let $Z_X=F_X(X)$ for a deterministic map $F_X$. Then
--
--   $$I(Z_X;X\mid T)=I(Z_X;S\mid T)+I(Z_X;X\mid S,T).$$
--
--   The information the representation keeps about the input beyond the task splits into a part shared with the self-supervised signal and a part that is superfluous even given the signal. The proofs of Theorems 2, 3 and 4 use this identity.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Appendix B, proof of Theorem 6 (= Theorem 2), first display, p. 13; reused in Appendix D, p. 14

import Mathlib
import Definitions.Def_SSLMultiView_Basic

open Real

namespace SSLMultiView

theorem cmi_input_decomposition {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    condMutualInfo P (rep F) inputX taskT =
      condMutualInfo P (rep F) signalS taskT + condMutualInfo P (rep F) inputX signalTask := by sorry

end SSLMultiView
