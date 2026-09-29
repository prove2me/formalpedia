-- Prove2me | Theorems.Thm_Rudin_ch07_weierstrass_M_test
-- name    : Rudin.ch07_weierstrass_M_test
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:13:31.673402+00:00
-- url     : https://prove2.me/theorems/3be1e311-3e09-4215-8bf9-5301718ef821
-- title:
--   Theorem 7.10 — the Weierstrass M-test
-- statement:
--   If $|f_n(x)| \le M_n$ for all $x \in E$ and $\sum M_n$ converges, then $\sum f_n$ converges uniformly on $E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 148, Theorem 7.10

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.10 (Weierstrass M-test): if `‖f n x‖ ≤ M n` on `E` and `∑ M n`
converges, then the series `∑ f n` converges uniformly on `E`. -/
theorem ch07_weierstrass_M_test {X : Type*} (E : Set X) (f : ℕ → X → ℂ) (M : ℕ → ℝ)
    (hbound : ∀ n, ∀ x ∈ E, ‖f n x‖ ≤ M n) (hM : Summable M) :
    ∃ g : X → ℂ,
      TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, f n x) g atTop E := by sorry

end Rudin
