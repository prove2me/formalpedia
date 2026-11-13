-- Prove2me | Theorems.Thm_WatrousTQI_psd_supported_factorization
-- name    : WatrousTQI.psd_supported_factorization
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-12T22:35:04.15318+00:00
-- url     : https://prove2.me/theorems/21cdf29d-7f81-4d8d-8031-f51abec5c70f
-- title:
--   Lemma 2.30 — positive operators supported on a matrix range
-- statement:
--   For arbitrary positive dimensions $n,m$, any complex $n\times m$ matrix $A$, and any complex $n\times n$ matrix $P$, $$P\succeq0\ \text{and}\ \operatorname{im}P\subseteq\operatorname{im}A\quad\Longleftrightarrow\quad \exists Q\succeq0:\ P=AQA^\dagger.$$ No injectivity, invertibility, or full-rank hypothesis is imposed on $A$. This is the range factorization needed to describe positive operators supported on a Choi matrix's support.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Section 2.2.4, printed pp.96–99. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Lemma 2.30, equation (2.171), printed p.96.

import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace WatrousTQI
theorem psd_supported_factorization {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin m) ℂ) (P : Matrix (Fin n) (Fin n) ℂ) :
    (P.PosSemidef ∧ LinearMap.range P.mulVecLin ≤ LinearMap.range A.mulVecLin) ↔
      ∃ Q : Matrix (Fin m) (Fin m) ℂ, Q.PosSemidef ∧ P = A * Q * Aᴴ := by sorry
end WatrousTQI
