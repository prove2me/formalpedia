-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_authentication_availability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.authentication_availability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:22:33.407237+00:00
-- url     : https://prove2.me/theorems/a61b588b-427d-4a58-b38e-9fbc41c0a9e9
-- title:
--   D.1: honest authentication is identity
-- statement:
--   Let $\{h_k:X\to T\}_{k\in K}$ be any hash family with a finite nonempty key alphabet $K$. Alice and Bob share an ideal uniform key, Alice sends $(x,h_k(x))$, and the honest forwarding filter delivers exactly that pair to Bob. Bob accepts the message if and only if the received tag equals $h_k$ of the received message. The complete filtered output law is
--
--   $$\Pr[\text{Bob outputs }z\mid x]=\begin{cases}1,&z=x,\\0,&\text{otherwise},\end{cases}$$
--
--   and the probability of an error output is zero. Thus the honest real and ideal channels are both the identity. No universality assumption or malicious authentication security is asserted.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 50, D.1: honest authentication is identity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.49--50, Appendix D.1: with honest forwarding filters, authentication
is the identity channel for every hash family. The ideal shared key is uniform
and nonempty; no malicious-channel security conclusion is included. -/
theorem authentication_availability {K X T : Type*} [Fintype K] [Nonempty K]
    [DecidableEq X] [DecidableEq T] (h : K → X → T) (x : X) :
    honestAuthentication h x = (fun out => if out = some x then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
