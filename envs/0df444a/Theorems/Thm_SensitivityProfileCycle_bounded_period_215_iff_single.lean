-- Prove2me | Theorems.Thm_SensitivityProfileCycle_bounded_period_215_iff_single
-- name    : SensitivityProfileCycle.bounded_period_215_iff_single
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-24T13:41:05.547594+00:00
-- url     : https://prove2.me/theorems/f6083780-4473-4a57-b3f6-8d78b8ed4506
-- title:
--   A bounded-period family approaching 2.15 contains an exact crossing
-- statement:
--   For a finite sensitivity profile certificate with $K$ vertices, period $p$, and radius $R>1$, put $Y=(K^p)^{20}$. Suppose $R^{43k+42}\le Y^{k+1}$. If $uY\le k+1$ and $R<2^u$, then $R^{43}\le Y$. Consequently, there exist certificates approaching exponent $43/20$ at every prescribed accuracy with a common upper bound on their periods if and only if a single finite certificate attains the non-strict crossing $R^{43}\le (K^p)^{20}$.
-- source:
--   The certificate is SensitivityProfileCycle.Certificate, as used in the 2.15 target. The regular-tournament degree count and the coarse degree estimate are reused from the proved fixed-vertex result https://prove2.me/theorems/fb05e74d-6d1c-4e5d-a7c6-078e11b68921 . The quantitative integer-gap test and its bounded-period consequence are new.

import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.bounded_period_215_iff_single :
    (∀ (C : SensitivityProfileCycle.Certificate) (k u : ℕ), 1 < C.radius →
      C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1)) →
      u*(C.vertices^C.period)^20 ≤ k+1 → C.radius < 2^u →
      C.radius^43 ≤ (C.vertices^C.period)^20) ∧
    ((∃ L : ℕ, ∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
        C.period ≤ L ∧ 1 < C.radius ∧
        C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1))) ↔
      ∃ C : SensitivityProfileCycle.Certificate, 1 < C.radius ∧
        C.radius^43 ≤ (C.vertices^C.period)^20) := by sorry
