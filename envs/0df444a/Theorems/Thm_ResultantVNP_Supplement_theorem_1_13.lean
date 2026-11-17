-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_1_13
-- name    : ResultantVNP.Supplement.theorem_1_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:59:41.124965+00:00
-- url     : https://prove2.me/theorems/d13d79f7-9f17-4a24-bbbd-71032b757f35
-- title:
--   Theorem 1.13 — $\exists\mathbb R\subseteq\mathsf{CH}$
-- statement:
--   The existential theory of the reals lies in the counting hierarchy:
--   $$\exists\mathbb R\subseteq\mathsf{CH}.$$
--   Here $\exists\mathbb R$ is, as on p.4 of the paper, the class of languages that reduce in polynomial time (many-one) to ETR, the set of true existential sentences over the reals. $\mathsf{CH}=\bigcup_{k\ge0}\mathsf C_k\mathsf P$ with $\mathsf C_0\mathsf P=\mathsf P$ and $\mathsf C_{k+1}\mathsf P=\mathsf{PP}^{\mathsf C_k\mathsf P}$.
--
--   $\exists\mathbb R$ was known to be contained in $\mathsf{PSPACE}$ (Canny 1988). The theorem places real feasibility in the counting hierarchy.
--
--   **Formalization Note** ETR and CH are the published definitions (`ETRLanguage`, `InCH`).
--
--   Differences from the source:
--   - encoding: existential sentences whose polynomial comparisons have binary integer coefficients and exponents (p.13) → terms built from $0$, $1$, $+$, $\times$ in the published `ETRLanguage`; reason: binary integer constants and binary exponents (by repeated squaring through fresh existential variables) are expressible in polynomial size, and differences of polynomials are comparisons of two sides, so the two ETR languages reduce to each other in polynomial time and the class $\exists\mathbb R$ is unchanged.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.13, p.7; ∃R, p.4; Definition 6.1, p.24

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Supplement_ExistentialReals

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Theorem 1.13.** `∃R ⊆ CH`: every language that polynomial-time many-one reduces to the
existential theory of the reals lies in the counting hierarchy.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.13, p.7 (proof Section 6, pp.24–32, and Appendix D).

**Formalization Note** `∃R` is the class of p.4: "The class ∃R consists of the decision problems
that reduce to this theory under polynomial-time many-one reductions", with ETR the published
`ETRLanguage` (true existential sentences over the reals in a binary code). `CH` is the published
`InCH`: `C₀P = P`, `C_{k+1}P = PP^{C_kP}`, `CH = ⋃_k C_kP` (Definition 6.1, p.24). -/
theorem theorem_1_13 :
    ∀ L : Language, ManyOneReduction L ApproxPolySatCH.Main.Supplement.ETRLanguage → InCH L := by sorry

end Supplement

end ResultantVNP
