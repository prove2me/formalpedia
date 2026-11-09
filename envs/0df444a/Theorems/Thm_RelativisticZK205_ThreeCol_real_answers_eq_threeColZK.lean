-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_real_answers_eq_threeColZK
-- name    : RelativisticZK205.ThreeCol.real_answers_eq_threeColZK
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:51.10413+00:00
-- url     : https://prove2.me/theorems/0e2b948e-4b31-4bff-9e1b-7085fa20a115
-- title:
--   Proof of Theorem 1 (p.11) — the real provers' answers have the law of 3-COLZK
-- statement:
--   Let $c$ be a proper 3-colouring of $G$ and let $((i,j),r)$, $((i',j'),r')$ be edge queries. Define the match pattern $m_{uv}=1$ if the $u$-th vertex of the first query equals the $v$-th vertex of the second (the $0$-th vertices being $i,i'$ and the $1$-st being $j,j'$), and $0$ otherwise. Then the joint law of the real provers' answers $((w_i,w_j),(w'_{i'},w'_{j'}))$ in $\Pi^{(2)}_{\mathrm{LHV}}[G,c]$ equals the law of the 3-COLZK outputs $((\ell_0,\ell_1),(\ell'_0,\ell'_1))$ on inputs $(m,r)$ and $(0,r')$:
--
--   $$
--   \Pr\big[(w_i,w_j)=(\ell_0,\ell_1),\ (w'_{i'},w'_{j'})=(\ell'_0,\ell'_1)\big]=P_{\text{3-COLZK}}\big(\ell_0,\ell_1,\ell'_0,\ell'_1\,\big|\,(m,r),(0,r')\big).
--   $$
--
--   Uniform masks and the random relabelling $\Pi$ of colours make the answers uniform over exactly the outputs that 3-COLZK allows; properness of $c$ is what makes $w_i+w'_i\ne w_j+w'_j$ when the same edge is asked with $r\ne r'$.
--
--   Differences from the source:
--   - reading: the real prover's answers are uniform over precisely the outputs allowed by the 3-COLZK channel → equality of the real joint answer law with the law of 3-COLZK on inputs (m, r) and (0, r′), mapped to non-aborting replies; reason: 3-COLZK depends on its inputs only through z ⊕ z′ and r ⊕ r′, and m is the pattern whose shares the simulators compute
--   - encoding: a graph G = (V, E) whose vertices are labelled by distinct integers 0, …, |V|−1, with a 3-colouring C = {(i, c_i)}, c_i ∈ F₃, (i, j) ∈ E ⇒ c_j ≠ c_i → G : SimpleGraph (Fin n) with decidable adjacency, c : Fin n → ZMod 3 with G.Adj x y → c x ≠ c y; bits of F₂ are Bool; reason: the same graphs and colourings; Fin n is the label set {0, …, n−1}
--   - encoding: (i, j) ∈ E, edges always represented with i < j → IsValid G (i, j, r) := i < j ∧ G.Adj i j; reason: the source's own convention for membership of an ordered pair in E (p.9)
--   - encoding: indices u, v ∈ {0, 1}, inputs (z_00, z_01, z_10, z_11, r), outputs in Z_3^2 → u, v : Bool, inputs (Bool → Bool → Bool) × Bool, outputs ZMod 3 × ZMod 3; reason: the same finite alphabets
--   - encoding: a valid query returns a pair of elements of F₃; an invalid query aborts → Reply := Option (ZMod 3 × ZMod 3), with some for a pair and none for abort; reason: the option constructor distinguishes the same response and abort events; mapping both valid answers with some preserves their joint law
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, proof of Theorem 1 ("Uniform masks and random colour relabelling …")

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_ThreeColZK
import Definitions.Def_RelativisticZK205_ThreeCol_Protocol

namespace RelativisticZK205.ThreeCol

/-- Proof of Theorem 1, p.11: for a proper 3-colouring and two edge queries `((i, j), r)`,
`((i', j'), r')`, the real provers' joint answers have exactly the law of the 3-COLZK outputs on the
match pattern `m_uv = [label u of the first query = label v of the second]` (label `0` is `i` or
`i'`, label `1` is `j` or `j'`) and the bits `r, r'`, both answers being non-aborting. -/
theorem real_answers_eq_threeColZK {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → ZMod 3) (hc : ∀ x y, G.Adj x y → c x ≠ c y)
    (i j i' j' : Fin n) (r r' : Bool) (h₁ : IsValid G (i, j, r)) (h₂ : IsValid G (i', j', r')) :
    realChannel G c (i, j, r) (i', j', r') =
      (threeColZK
          (fun u v => decide (labelOf u (i, j, r) = labelOf v (i', j', r')), r)
          (fun _ _ => false, r')).map
        fun l => (some l.1, some l.2) := by sorry

end RelativisticZK205.ThreeCol
