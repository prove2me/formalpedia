-- Prove2me | Theorems.Thm_TongString_lorentz_anomaly_coefficient_vanishes_iff
-- name    : TongString.lorentz_anomaly_coefficient_vanishes_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:53:55.01154+00:00
-- url     : https://prove2.me/theorems/2f0b8883-dd0d-4eae-8c3d-665a50060519
-- title:
--   $[M^{i-},M^{j-}]$ coefficient vanishes at all levels iff $D=26$ and $a=1$
-- statement:
--   Let $D$ be a natural number (the spacetime dimension) and $a\in\mathbb R$ (the normal-ordering constant). In lightcone quantization the commutator of Lorentz generators is
--
--   $$
--   [M^{i-},M^{j-}]=\frac{2}{(p^+)^2}\sum_{n>0}c_n\,\bigl(\alpha^i_{-n}\alpha^j_n-\alpha^j_{-n}\alpha^i_n\bigr)+(\alpha\leftrightarrow\tilde\alpha),\qquad c_n=\Big[\frac{D-2}{24}-1\Big]n+\frac1n\Big[a-\frac{D-2}{24}\Big].
--   $$
--
--   The coefficients vanish at every level,
--
--   $$
--   c_n=0\quad\text{for all integers } n\ge1,
--   $$
--
--   if and only if $D=26$ and $a=1$. This is the final step of Tong's "more rigorous" lightcone argument that the relativistic string can only be quantized in flat Minkowski space if $D=26$ and $a=1$.
--
--   **Formalization Note** Only the coefficient identity is formalized; the operator formula for $[M^{i-},M^{j-}]$ is quoted by Tong without derivation and is not part of this statement.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 2.4 'Lorentz Invariance Revisited', pp. 47–48 (formula for [M^{i−}, M^{j−}] and 'D = 26 and a = 1')

import Mathlib

namespace TongString

theorem lorentz_anomaly_coefficient_vanishes_iff (D : ℕ) (a : ℝ) :
    (∀ n : ℕ, 0 < n →
        (((D : ℝ) - 2) / 24 - 1) * n + 1 / (n : ℝ) * (a - ((D : ℝ) - 2) / 24) = 0) ↔
      (D = 26 ∧ a = 1) := by sorry

end TongString
