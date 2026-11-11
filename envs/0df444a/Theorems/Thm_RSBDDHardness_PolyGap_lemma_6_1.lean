-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_lemma_6_1
-- name    : RSBDDHardness.PolyGap.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:08.330591+00:00
-- url     : https://prove2.me/theorems/8a7fa89c-cf66-45c7-ade3-8144f654732b
-- title:
--   Lemma 6.1 — pure powers span the extension
-- statement:
--   Throughout, $q$ is prime, $t\ge1$, $P\in\mathbb F_q[Z]$ is monic irreducible of degree $L=2t+1$, $\mathbb K=\mathbb F_q[Z]/(P)$, $\theta=Z\bmod P$ and $H=\operatorname{span}_{\mathbb F_q}\{1,\theta,\dots,\theta^t\}$ (the setting of §6.1).
--
--   If $2\le j<q$, then
--   $$\operatorname{span}_{\mathbb F_q}\{x^j:x\in H\}=\mathbb K.$$
--
--   So the first moment of elements of $H$ stays in $H$ while their higher powers span the whole field; this is the algebraic compatibility on which the construction rests.
--
--   Differences from the source:
--   - encoding: the standing setting of §6.1 (q prime, K = F_q[Z]/(P) with P monic irreducible of degree 2t+1, H = span{1, …, θ^t}) → explicit hypotheses on q, t ≥ 1 and P : Polynomial (ZMod q); K = AdjoinRoot P; reason: AdjoinRoot is the polynomial quotient with the power-basis coordinates of §6.1; primality, monicity, irreducibility and degree are explicit
--   - generalization: §6 opens with t = 2m from the nonempty cubic planar source formula and the field P constructed in §6.1 → every t ≥ 1 and every monic irreducible P of degree 2t+1 over the prime field; reason: every source field is included by taking t = 2m and its constructed P; the algebraic assertions use only the displayed power basis, and the condenser proof explicitly handles t = 1
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Lemma 6.1; setting of §6.1, PDF pp. 18–19, PDF p. 19 (printed p. 18); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Lemma 6.1 (Pure powers span the extension), PDF 19. In the setting of §6.1
(`q` prime, `t ≥ 1`, `𝕂 = 𝔽_q[Z]/(P)` with `P` monic irreducible of degree `2t+1`,
`H = span{1, θ, …, θ^t}`), if `2 ≤ j < q` then `span_{𝔽_q}{x^j : x ∈ H} = 𝕂`. -/
theorem lemma_6_1 (q t j : ℕ) (P : Polynomial (ZMod q)) (hq : q.Prime) (ht : 1 ≤ t)
    (hP : P.Monic) (hirr : Irreducible P) (hdeg : P.natDegree = 2 * t + 1)
    (hj : 2 ≤ j) (hjq : j < q) :
    powSpan P (Hsp P t : Set (AdjoinRoot P)) j = ⊤ := by sorry

end RSBDDHardness.PolyGap
