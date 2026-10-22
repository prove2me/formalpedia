-- Prove2me | Theorems.Thm_ReadmissionsHRRP_HRRPI_lemma_1
-- name    : ReadmissionsHRRP.HRRPI.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:59.846736+00:00
-- url     : https://prove2.me/theorems/a1cd58a7-7346-4cc2-a27c-ba5f61fe9199
-- title:
--   Lemma 1, p. 11 — the welfare S has a unique maximizer (r*, c*) on the box, interior, satisfying the FOCs (3)–(4)
-- statement:
--   Consider the hospital model under its standing assumptions, with the interior-first-best hypothesis. The welfare
--   $$S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c)$$
--   has a unique maximizer $(r^*,c^*)$ over the box $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$. It satisfies $r^*\in(r_{\min},r_{\max})$, $c^*\in(c_{\min},c_{\max})$ and the first-order conditions
--   $$\lambda c^*+R_r(r^*,c^*)=0,\qquad \lambda(1+r^*)+R_c(r^*,c^*)=0 .$$
--
--   The point $(r^*,c^*)$ is the first-best benchmark: the readmission rate and marginal cost a fully informed regulator would impose. Proposition 1 compares the hospitals' equilibrium actions with it.
--
--   **Formalization Note** The maximization is over $B$ only: the paper's break-even constraint $\Pi(r,c)\ge 0$ involves the transfer $T$, which the regulator is free to choose, and does not restrict $(r,c)$. Interiority of the maximizer restates the `FirstBestInterior` hypothesis, which replaces the paper's Appendix A; existence, uniqueness and the first-order conditions are the content.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), p. 11, Lemma 1, (3)–(4)

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

namespace ReadmissionsHRRP.HRRPI

/-- Lemma 1 (p. 11): under the standing assumptions the welfare `S` of (2) has a unique maximizer
`(r*, c*)` over the box; it is interior and satisfies the first-order conditions (3)–(4). -/
theorem lemma_1 (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior) :
    ∃ xs : ℝ × ℝ, M.IsFirstBest xs ∧ (∀ x : ℝ × ℝ, M.IsFirstBest x → x = xs) ∧
      xs.1 ∈ Set.Ioo M.rmin M.rmax ∧ xs.2 ∈ Set.Ioo M.cmin M.cmax ∧
      M.lam * xs.2 + M.Rr xs.1 xs.2 = 0 ∧
      M.lam * (1 + xs.1) + M.Rc xs.1 xs.2 = 0 := by sorry

end ReadmissionsHRRP.HRRPI
