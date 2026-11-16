-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_37
-- name    : QThermalClassical.Supplement.theorem_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:43:58.008578+00:00
-- url     : https://prove2.me/theorems/62c236ad-15d7-499f-994d-90734c63412f
-- title:
--   Theorem 37 — $-h\sum_iZ_i-(g/w(n))\prod_iX_i$ is entangled at every constant $\beta$ for large $n$, with weighted strength $hw(1)+g$
-- statement:
--   Let $g,h,\beta>0$ and let $w:\mathbb N\to\mathbb R$ be non-decreasing with $w(n)=e^{o(n)}>0$ (i.e. $w>0$ and $\log w(n)=o(n)$). On $n$ qubits let
--   $$
--   H_n=\sum_{a\in A}h_a=-h\sum_iZ_i-\frac{g}{w(n)}\prod_iX_i.\tag{433}
--   $$
--   Then $\rho_\beta(H_n)$ is entangled for all sufficiently large $n$, and for every $n\ge1$
--   $$
--   \sup_x\sum_{a:\ x\in\mathrm{supp}(h_a)}\|h_a\|\,w(|\mathrm{supp}(h_a)|)=h\,w(1)+g<\infty.\tag{434}
--   $$
--
--   This is the witness for the converse of Theorem 1(c): no subexponential weight on the support size forces separability at a constant temperature.
--
--   Differences from the source:
--   - reading: $w(n)=e^{o(n)}>0$ → $w>0$ and $\log w(n)=o(n)$; reason: $w=e^f$ with $f=o(n)$ is exactly this
--   - encoding: $\|h_a\|$ for the term $h_a=c_aP_a$; $\sup_x$; entangled → $|c_a|$; real supremum over `Fin n`, $n\ge1$; not in $\mathrm{Sep}_n$; reason: Pauli strings have operator norm $1$; (434) concerns $n\ge1$ qubits; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 37, eqs. (433)–(434), p.88

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_Supplement_weightedStrength
import Definitions.Def_QThermalClassical_Supplement_thm37Coeff

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 37 (Entangled nonlocal Hamiltonians).** For all constants `g, h, β > 0` and every
non-decreasing `w : ℕ → ℝ` with `w(n) = e^{o(n)} > 0`, the Gibbs state of
`H_n = −h Σ_i Z_i − (g/w(n)) Π_i X_i` (433) on `n` qubits is entangled for all sufficiently
large `n`; and for every `n ≥ 1`, `sup_x Σ_{a : x ∈ supp h_a} ‖h_a‖ w(|supp h_a|) = h w(1) + g`
(434).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 37, eqs. (433)–(434), p.88.

**Formalization Note.** `w(n) = e^{o(n)} > 0` is `w > 0` and `log w(n) = o(n)`. For a term
`h_a = c_a P_a`, `‖h_a‖ = |c_a|` (Pauli strings have operator norm `1`). The supremum over
qubits is the real `⨆` over `Fin n`, `n ≥ 1`. "Entangled" is "not in `Sep_n`" of (7). -/
theorem theorem_37 (g h β : ℝ) (hg : 0 < g) (hh : 0 < h) (hβ : 0 < β) (w : ℕ → ℝ)
    (hw : Monotone w) (hwpos : ∀ m, 0 < w m)
    (hwo : (fun m : ℕ => Real.log (w m)) =o[Filter.atTop] (fun m : ℕ => (m : ℝ))) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ IsSeparable (gibbs (ham (thm37Coeff n h g w)) β)) ∧
    (∀ n : ℕ, 1 ≤ n → ⨆ x : Fin n, weightedStrength w (thm37Coeff n h g w) x = h * w 1 + g) := by sorry

end QThermalClassical.Supplement
