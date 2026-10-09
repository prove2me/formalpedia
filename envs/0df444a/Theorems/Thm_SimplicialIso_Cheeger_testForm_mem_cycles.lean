-- Prove2me | Theorems.Thm_SimplicialIso_Cheeger_testForm_mem_cycles
-- name    : SimplicialIso.Cheeger.testForm_mem_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:09.236811+00:00
-- url     : https://prove2.me/theorems/6d815fcc-f126-4f7f-a653-cbf95ce91d92
-- title:
--   §4.1, p. 12 — the test form f of (4.1) is a (d−1)-cycle, f ∈ Z_{d−1}
-- statement:
--   Let $d\ge1$ and let $A_0,\dots,A_d$ be a partition of the vertex set $V=\{0,\dots,n-1\}$ into nonempty sets. On the complete $(d-1)$-skeleton, the test form $f\in\Omega^{d-1}$ of (4.1) is a $(d-1)$-cycle:
--   $$\partial_{d-1} f = 0,\qquad\text{i.e. } f\in Z_{d-1}.$$
--   This is the step of the proof of Theorem 1.2 that makes $f$ admissible in the Rayleigh quotient for the spectral gap, which is taken over $Z_{d-1}$.
--
--   **Formalization Note.** $\partial_{d-1}$ is the boundary on the complete skeleton, so the statement does not involve the $d$-cells of $X$. $d\ge1$ is a disclosed addition.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 12, §4.1, "We proceed to show that f ∈ Z_{d−1}"

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting
import Definitions.Def_SimplicialIso_Cheeger_TestForm

namespace SimplicialIso.Cheeger

theorem testForm_mem_cycles (n d : ℕ) (hd : 1 ≤ d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : IsPartition A) :
    testForm A ∈ cycles n d := by sorry

end SimplicialIso.Cheeger
