-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_conversion_criterion
-- name    : SuperactivatedCheating.StateConversion.conversion_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:08.023775+00:00
-- url     : https://prove2.me/theorems/988d8688-8158-4c1d-ad43-ed2c84ff23b6
-- title:
--   Proof of Theorem 11, p. 15 — exact local conversion criterion
-- statement:
--   A probability vector is a finitely indexed nonnegative real vector summing to 1. $(u\otimes v)_{(i,j)}=u_iv_j$ and $p^{\otimes n}_x=\prod_i p_{x_i}$ for strings $x$ of length $n$. "$u=v$ up to a permutation" for vectors of possibly different lengths means that their multisets of nonzero entries coincide. For probability vectors $p\in\mathbb R^k$, $q\in\mathbb R^l$, the state-conversion game $G_{SC}(p,q)$ has trivial referee register, question state $|\psi_p\rangle=\sum_i\sqrt{p_i}\,|i,i\rangle$ and accepting projection $|\phi_q\rangle\langle\phi_q|$ with $|\phi_q\rangle=\sum_j\sqrt{q_j}\,|j,j\rangle$. The witnesses are $q=(1/3,2/3)$ and $p=\frac1{201}(1,2,2,4,4,4,8,16,32,32,32,64)$, and the polynomials are $S(x)=1+x+2x^2-x^3+2x^4+x^5$ and $P(x)=(1+x)S(x)$ over $\mathbb Z$.
--
--   Let $p\in\mathbb R^k$ and $q\in\mathbb R^l$ be probability vectors. There exist local channels $\mathcal E,\mathcal F:L(\mathbb C^k)\to L(\mathbb C^l)$ (finite normalized Kraus families of any rank) with $(\mathcal E\otimes\mathcal F)(|\psi_p\rangle\langle\psi_p|)=|\phi_q\rangle\langle\phi_q|$ if and only if there is a probability vector $r$ of some finite length $d$ with $p=q\otimes r$ up to a permutation.
--
--   Differences from the source:
--   - encoding: quantum channels (CPTP maps) E : L(H_A) → L(H_a), F : L(H_B) → L(H_b) → finite normalized Kraus families of any finite rank (QAlgorithms.IsKrausFamily), with E ⊗ F ⊗ id_R given by the Kraus family E_j ⊗ F_k ⊗ I_R; reason: in finite dimension the CPTP maps are exactly the maps with a finite normalized Kraus family (p. 10); every rank is allowed, so no channel is lost
--   - reading: exact conversion under local operations and shared randomness (LOSR), Definition 12 item 4 → local channels E ⊗ F with no shared randomness; reason: §2.1's local strategy has no shared randomness; for a pure target state a convex mixture of local conversions is exact only if every branch is, so the two notions coincide
--   - reading: p = q ⊗ r up to a permutation → the multisets of nonzero entries of p and of q ⊗ r coincide; reason: the vectors have different lengths and zero entries carry no Schmidt coefficient; a literal bijection of full index sets would make the criterion false (p = (1/2, 1/2, 0) converts to q = (1/2, 1/2) by local relabelling, yet 3 is not a multiple of 2)
--   - encoding: 1-based indices i, j → 0-based Fin k, Fin l; reason: relabelling only
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, proof of Theorem 11, p. 15

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_GameSC

namespace SuperactivatedCheating.StateConversion

/-- Proof of Theorem 11, p. 15: the exact local conversion criterion. For probability vectors
`p` on `Fin k` and `q` on `Fin l`, there are local channels `E, F : L(ℂ^k) → L(ℂ^l)` with
`(E ⊗ F)(|ψ_p⟩⟨ψ_p|) = |ϕ_q⟩⟨ϕ_q|` if and only if `p = q ⊗ r` up to a permutation for some
probability vector `r` of some finite length. -/
theorem conversion_criterion {k l : ℕ} (p : Fin k → ℝ) (q : Fin l → ℝ)
    (hp : IsProbVec p) (hq : IsProbVec q) :
    (∃ S : LocalStrategy (Fin k) (Fin k) (Fin l) (Fin l),
        outputState (psiP p) S = pureState (phiQ q)) ↔
      ∃ (d : ℕ) (r : Fin d → ℝ), IsProbVec r ∧ EqUpToPerm p (vtensor q r) := by sorry

end SuperactivatedCheating.StateConversion
