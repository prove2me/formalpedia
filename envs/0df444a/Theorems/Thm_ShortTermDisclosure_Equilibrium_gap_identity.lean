-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_gap_identity
-- name    : ShortTermDisclosure.Equilibrium.gap_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:31.237693+00:00
-- url     : https://prove2.me/theorems/c9dec7b3-e5fe-45c0-9221-5cbefcff2add
-- title:
--   Equation (19) — lower threshold and gap identity
-- statement:
--   For $0<\lambda<1$ and $v_2<\bar\mu$, the lower threshold equation
--
--   $$\lambda\bar\mu+\frac{1-\lambda}{2}v_1-\frac{1+\lambda}{2}v_2=0$$
--
--   is equivalent to $v_1=\frac{1+\lambda}{1-\lambda}v_2-\frac{2\lambda}{1-\lambda}\bar\mu$ and implies
--
--   $$v_2-v_1=\frac{2\lambda}{1-\lambda}(\bar\mu-v_2)>0.$$
--
--   This identifies the positive width of the two-tailed withholding interval.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), pp. 38–39 (PDF 41–42), (19) and proof of Proposition 2

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem gap_identity (ell muhi v1 v2 : ℝ)
    (hell0 : 0 < ell) (hell1 : ell < 1) (hm : v2 < muhi) :
    (ell * muhi + (1 - ell) / 2 * v1 - (1 + ell) / 2 * v2 = 0 ↔
      v1 = (1 + ell) / (1 - ell) * v2 - 2 * ell / (1 - ell) * muhi) ∧
    (ell * muhi + (1 - ell) / 2 * v1 - (1 + ell) / 2 * v2 = 0 →
      v2 - v1 = 2 * ell / (1 - ell) * (muhi - v2) ∧ 0 < v2 - v1) := by sorry

end ShortTermDisclosure.Equilibrium
