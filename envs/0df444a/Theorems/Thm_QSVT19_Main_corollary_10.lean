-- Prove2me | Theorems.Thm_QSVT19_Main_corollary_10
-- name    : QSVT19.Main.corollary_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:31.202987+00:00
-- url     : https://prove2.me/theorems/cce5b1b4-b3e3-48b7-a9bd-c9ddf836e058
-- title:
--   Corollary 10: real quantum signal processing
-- statement:
--   Let $d\ge1$ and let $P_\Re\in\mathbb R[x]$ have degree $d$ and parity $d\bmod 2$, with
--   $$|P_\Re(x)|\le1\quad\text{for all }x\in[-1,1].$$
--   Then there is $P\in\mathbb C[x]$ with $\Re[P]=P_\Re$ that satisfies the requirements of Corollary 8 (degree $d$, parity $d\bmod2$, $|P|\le1$ on $[-1,1]$, $|P|\ge1$ for $|x|\ge1$, and $P(ix)P^*(ix)\ge1$ when $d$ is even).
--
--   Combined with Corollary 8, every such real polynomial is the real part of a polynomial realized by reflection-based quantum signal processing.
--
--   **Formalization Note** The printed sentence omits $\Re[P]=P_\Re$, without which the statement is trivial (the Chebyshev polynomial $T_d$ meets Corollary 8's requirements). The proof of Corollary 18 uses exactly this reading. The running-time ("Moreover") claim is not included.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 14, Corollary 10 (existence claim)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 10, p. 14: "Let P_ℜ(x) ∈ R[x] be a degree-d polynomial for some d ≥ 1, such
that • P_ℜ has parity-(d mod 2), and • for all x ∈ [−1, 1]: |P_ℜ(x)| ≤ 1.
Then there exists P ∈ C[x] that satisfies the requirements of Corollary 8."

**Formalization Note.** The printed sentence omits `ℜ[P] = P_ℜ`, without which the claim is
trivial (the Chebyshev polynomial `T_d` satisfies the requirements of Corollary 8, by Lemma 9).
The intended claim, used in the proof of Corollary 18 (p. 19: "By Corollary 10 we can find a
Φ ∈ R^n such that ℜ[P] = P_ℜ") and implicit in Corollary 10's own "Moreover" clause, is stated:
`∃ P, ℜ[P] = P_ℜ` and `P` meets Corollary 8's requirements. "degree-d" is `natDegree = d`; the
parity of the real polynomial is that of its image in `ℂ[X]`. The "Moreover" clause (classical
running time) is not part of this statement. -/
theorem corollary_10 (d : ℕ) (hd : 1 ≤ d) (PR : ℝ[X]) (hdeg : PR.natDegree = d) (hpar : QAlgorithms.HasParity (PR.map Complex.ofRealHom) d) (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ P : ℂ[X], RePartEq P PR ∧ Cor8Requirements d P := by sorry

end QSVT19.Main
