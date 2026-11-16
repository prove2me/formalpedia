-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_36
-- name    : QThermalClassical.Supplement.theorem_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:43:32.807193+00:00
-- url     : https://prove2.me/theorems/37caaf96-2ba9-460e-a96c-2e9b49688973
-- title:
--   Theorem 36 — long-range Pauli Hamiltonians with prescribed $w_{\mathrm{free}},w_{\mathrm{pert}}$ have magic above (424); hence $\beta_{\mathrm{stab}}(s,k;\epsilon)=O(\log(1/\epsilon)/sk)$
-- statement:
--   1. For every integer $k\ge2$ and $w_{\mathrm{free}},w_{\mathrm{pert}}>0$ there is a $((w_{\mathrm{free}}+w_{\mathrm{pert}})/k,\,k)$-long-range Pauli Hamiltonian $H$ with a decomposition $H=H_0+V$ whose anticommutation parameters (34) are exactly $w_{\mathrm{free}}$ and $w_{\mathrm{pert}}$, and whose Gibbs state has magic ($\rho_\beta(H)\notin\mathrm{STAB}_n$) for all
--   $$
--   \beta>\frac1{\sqrt{w_{\mathrm{pert}}^2+w_{\mathrm{free}}^2}}\,\mathrm{artanh}\frac{\sqrt{w_{\mathrm{pert}}^2+w_{\mathrm{free}}^2}}{w_{\mathrm{pert}}+w_{\mathrm{free}}}.\tag{424}
--   $$
--   2. Hence $\beta_{\mathrm{stab}}(s,k;\epsilon)=O(\log(1/\epsilon)/sk)$: there are $C>0$ and $\epsilon_0\in(0,1)$ such that for all $\epsilon\in(0,\epsilon_0)$, $s>0$ and integers $k\ge2$,
--   $$
--   \beta_{\mathrm{stab}}(s,k;\epsilon)\le C\,\frac{\log(1/\epsilon)}{sk},
--   $$
--   and every $r$ in the set (10) defining $\beta_{\mathrm{stab}}(s,k;\epsilon)$ satisfies the same bound.
--
--   This is the upper half of Theorem 3's death-of-magic threshold.
--
--   Differences from the source:
--   - reading: with anticommutation parameters $w_{\mathrm{free}},w_{\mathrm{pert}}$ → some decomposition $H=H_0+V$ has exactly these values of (34); reason: (34) is defined per decomposition; the proof exhibits one
--   - reading: Hence, $\beta_{\mathrm{stab}}(s,k;\epsilon)=O(\log(1/\epsilon)/sk)$ → $\exists C>0,\ \epsilon_0\in(0,1),\ \forall\epsilon\in(0,\epsilon_0),\ \forall s>0,\ \forall k\ge2$: every element of the set (10) and its supremum are $\le C\log(1/\epsilon)/(sk)$; reason: the proof's regime 'for asymptotically small $\epsilon$' (p.88); constants uniform in $s,k$; bounding every element excludes the value $0$ of a real supremum of an unbounded set
--   - encoding: $k$; $n$ qubits ($k^2$ in the proof); Pauli strings of $H_0$, $V$; $\mathrm{STAB}_n$ → $k\in\mathbb N$; some `Fin n`; coefficient functions without identity term; plain convex hull of pure stabilizer states; reason: an identity term changes neither (33) nor the infimum (35); no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 36, eq. (424), p.87; eq. (10), p.11; eqs. (32)–(35) and Definition 2.6, p.16

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_Supplement_STAB
import Definitions.Def_QThermalClassical_Supplement_epsClose
import Definitions.Def_QThermalClassical_Supplement_betaStab

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 36 (Long-range Pauli Hamiltonian magic).**
1. For every integer `k ≥ 2` and `w_free, w_pert > 0` there is a
   `((w_free + w_pert)/k, k)`-long-range Pauli Hamiltonian `H` with a decomposition
   `H = H₀ + V` (32) whose anticommutation parameters (34) are `w_free` and `w_pert`, and whose
   Gibbs state has magic (is not in `STAB_n`) for all
   `β > (1/√(w_pert² + w_free²)) artanh(√(w_pert² + w_free²)/(w_pert + w_free))` (424).
2. Hence `β_stab(s, k; ε) = O(log(1/ε)/(sk))`: there are `C > 0` and `ε₀ ∈ (0, 1)` such that for
   all `ε ∈ (0, ε₀)`, `s > 0` and integers `k ≥ 2`, every element of the set (10) defining
   `β_stab(s, k; ε)`, and so `β_stab(s, k; ε)` itself, is at most `C log(1/ε)/(sk)`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 36, eq. (424), p.87; `β_stab` (10), p.11; (32)–(35), Definition 2.6, p.16.

**Formalization Note.** "Anticommutation parameters `w_free, w_pert`" means a decomposition with
exactly these values of (34). `β_stab(s, k; ε)` is `β_stab` of the family of `(s, k)`-long-range
Pauli Hamiltonians that are `ε`-close to commuting (Definition 2.6). The `O(·)` is read for
asymptotically small `ε` (the proof's regime), with constants uniform in `s` and `k`; bounding
every element of the set rules out the junk value of `sSup` on an unbounded set. -/
theorem theorem_36 :
    (∀ k : ℕ, 2 ≤ k → ∀ wf wp : ℝ, 0 < wf → 0 < wp →
      ∃ (n : ℕ) (c u v : PauliWord (Fin n) → ℝ),
        IsLongRangePauli ((wf + wp) / k) (k : ℝ) c ∧ IsDecomposition c u v ∧
        wFree u v = wf ∧ wPert u v = wp ∧
        ∀ β : ℝ, 1 / Real.sqrt (wp ^ 2 + wf ^ 2) *
            Real.artanh (Real.sqrt (wp ^ 2 + wf ^ 2) / (wp + wf)) < β →
          gibbs (ham c) β ∉ STAB) ∧
    (∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ s : ℝ, 0 < s → ∀ k : ℕ, 2 ≤ k →
        (∀ r ∈ betaStabSet s (k : ℝ) ε, r ≤ C * Real.log (1 / ε) / (s * k)) ∧
        betaStab s (k : ℝ) ε ≤ C * Real.log (1 / ε) / (s * k)) := by sorry

end QThermalClassical.Supplement
