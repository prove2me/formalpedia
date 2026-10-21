-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_partially_assisted_inner_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.partially_assisted_inner_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:17:39.827841+00:00
-- url     : https://prove2.me/theorems/0f4d9534-a972-4bf5-85f1-ea27dcb244f8
-- title:
--   Theorem 5: Bob-only assisted superposition inner bound
-- statement:
--   Let $\mathcal N:A\to B\otimes C$ be any CPTP quantum broadcast channel on nonzero finite-dimensional registers. Let $W$ be an arbitrary nonempty finite alphabet, $R$ an arbitrary nonzero finite reference, $p_W$ a distribution, and $\varphi_{RA}^w$ arbitrary density operators, which may be mixed. Set $\theta_{WRBC}=\sum_w p_W(w)\lvert w\rangle\langle w\rvert\otimes(\operatorname{id}_R\otimes\mathcal N)(\varphi_{RA}^w)$. Every nonnegative real rate pair satisfying
--
--   $$
--   R_B\le I(R;B\mid W)_\theta,\qquad R_C\le\min\{I(W;B)_\theta,I(W;C)_\theta\}
--   $$
--
--   is operationally achievable for partially entanglement-assisted classical communication. Conditional mutual information here is $\sum_w p_W(w)[H(R)_{\theta^w}+H(B)_{\theta^w}-H(RB)_{\theta^w}]$ in bits.
--
--   For every $0<\epsilon<1$, $\delta>0$ and every sufficiently large positive $n$, the conclusion gives codes with independent uniform messages of positive integer cardinalities, a fixed normalized possibly mixed shared state between Alice and Bob only, message-dependent CPTP encoders on Alice's share, a local POVM on Bob's share together with $B^n$, and a local POVM on $C^n$. Their average joint success is at least $1-\epsilon$ and the logarithmic message rates are at least $R_B-\delta,R_C-\delta$. Shared dimensions are arbitrary finite and unbudgeted; there is no assistance with Charlie or receiver communication. This is an inner bound for arbitrary channels, not a capacity equality and not restricted to Hadamard channels or pure ensembles.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 12, Theorem 5, §5.2: partially entanglement-assisted superposition inner bound for arbitrary broadcast channels

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF pp.12–13, Theorem 5, (97)–(99): the superposition inner bound for an
ARBITRARY CPTP broadcast channel with assistance only at Bob. Conditional RA
states may be mixed as in the printed statement, without a purity assumption.
The conclusion is operational achievability, rather than only capacity membership. -/
theorem partially_assisted_inner_bound {a b c w r : ℕ}
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) (channel : IsChannel N)
    (S : ReferenceEnsemble w r a) (RB RC : ℝ) (hB : 0 ≤ RB) (hC : 0 ≤ RC)
    (bob_bound : RB ≤ referenceMutualInfo S N)
    (charlie_bound : RC ≤ min (referenceBobLayer S N) (referenceCharlieLayer S N)) :
    (RB, RC) ∈ pairAchievable .partiallyAssisted N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
