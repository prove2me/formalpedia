-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_fcr_vs_dcr
-- name    : SharingPlatform.WageSchemes.fcr_vs_dcr
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:58.45061+00:00
-- url     : https://prove2.me/theorems/bfc91420-2a40-4202-903e-5886dc381abb
-- title:
--   Proof of Proposition 3, A.8, p. 52 (PDF 53) — α^{D*} < α^{F*} iff (13) holds, and p^{D*} < p^{F*} iff α^{D*} < α^{F*}
-- statement:
--   Assume the standing assumptions and $cl \ne bm$. Let $\alpha^{D*}$ be the DCR commission rate (5), $p^{D*}$ the DCR price (4), and let $\alpha \in (\bar\alpha, 1)$ be a zero of $f$ (the FCR commission rate of Lemma 2), with FCR price $p^F(\alpha) = \frac{a+k}{c+m(1-\alpha)}$. Write
--
--   $$Q(\alpha^{D*}) = \frac{b+c+l+m}{(b+c)(l+m)\alpha^{D*}} - \frac{b + (1-\alpha^{D*})l}{(1-\alpha^{D*})(cl-bm)}$$
--
--   for the left side of Inequality (13). Then:
--   1. $\alpha^{D*} < \alpha$ if and only if $Q(\alpha^{D*}) > 0$;
--   2. $\alpha < \alpha^{D*}$ if and only if $Q(\alpha^{D*}) < 0$;
--   3. $p^{D*} < p^F(\alpha)$ if and only if $\alpha^{D*} < \alpha$.
--
--   Together with the monotonicity of profit in price, this orders the DCR and FCR profits by the sign of (13).
--
--   **Formalization Note** The hypothesis $cl \ne bm$ makes the last denominator of $Q$ nonzero; $0 < \alpha^{D*} < 1$ holds by Lemma 1. Part 2 is the strict counterpart that the corrected case (c) of Proposition 3 uses. Part 3 rests on demand matching supply, which the page writes as $a - cp^* = -k + (1-\alpha^*)p^*$; the correct identity has the factor $m$, $-k + m(1-\alpha^*)p^*$.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, proof of Proposition 3, A.8, p. 52 (PDF 53), comparison of FCR and DCR, Inequality (13)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem fcr_vs_dcr (P : Params) (hP : P.Standing) (hcl : P.c * P.l ≠ P.b * P.m)
    (α : ℝ) (hα : α ∈ Set.Ioo (alphaBar P) 1) (hf : fFCR P α = 0) :
    (alphaD P < α ↔ 0 < cond13 P (alphaD P)) ∧
    (α < alphaD P ↔ cond13 P (alphaD P) < 0) ∧
    (pD P < priceFCR P α ↔ alphaD P < α) := by sorry
end SharingPlatform.WageSchemes
