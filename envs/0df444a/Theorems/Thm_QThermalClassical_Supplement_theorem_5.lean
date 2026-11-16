-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_5
-- name    : QThermalClassical.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:41:06.703384+00:00
-- url     : https://prove2.me/theorems/fbbfc2e6-d3a9-4728-ab78-118ac7e17266
-- title:
--   Theorem 5 — exponential decay of correlations for geometrically local $(s,k)$-long-range Pauli Hamiltonians
-- statement:
--   Let $H=\sum_{a\in A}c_aP_a$ be an $(s,k)$-long-range Pauli Hamiltonian ($s,k>0$) on a finite set of sites $\Lambda$ with distance $d$, with interaction range $R>0$:
--   $$
--   \max_{x,y\in\mathrm{supp}(P_a)}d(x,y)\le R\qquad\text{for every } a\in A. \tag{40}
--   $$
--   Let $A,B$ be Hermitian observables supported on disjoint sets $X,Y\subset\Lambda$. Then for
--   $$
--   0\le\beta\le\frac1{128e\,\max\Big\{s,\sqrt{s\,\max_{a\in A}|c_a|\,\max\{k,|X|+|Y|\}}\Big\}}\tag{41}
--   $$
--   it holds that
--   $$
--   \big|\langle AB\rangle_\beta-\langle A\rangle_\beta\langle B\rangle_\beta\big|\le48\cdot2^{|X|+|Y|}\,\|A\|\,\|B\|\,\exp\Big(-\frac{\log8}{6R}\,d(X,Y)\Big),\tag{42}
--   $$
--   where $\langle O\rangle_\beta=\mathrm{Tr}(O\rho_\beta(H))$, $\|\cdot\|$ is the operator norm and $d(X,Y)=\min_{x\in X,y\in Y}d(x,y)$.
--
--   Correlations decay exponentially throughout the infinite-temperature phase, at any separation of the observables; this resolves open question 1(a) of [HMS20].
--
--   Differences from the source:
--   - generalization: a lattice $\Lambda\subset\mathbb Z^D$ with Euclidean distance $d$ (§5.4) → any finite metric space of sites; reason: the proof (Corollary 27 and the proof of Theorem 5, pp.61–62) uses only (40) and the triangle inequality; a finite subset of $\mathbb Z^D$ with Euclidean distance is an instance
--   - encoding: interaction range $R$ in $\log 8/(6R)$ → $R>0$; reason: $\log8/(6R)$ is undefined at $R=0$; only that undefined case is excluded
--   - encoding: $d(X,Y)$ for $X$ or $Y$ empty (undefined) → the value $0$; reason: an observable supported on $\emptyset$ is a scalar multiple of $I$, whose covariance with any observable is $0$, so the bound holds for any value
--   - encoding: $\max_{a\in A}|c_a|$; $\langle\cdot\rangle_\beta$; $\|\cdot\|$ → maximum over all Pauli words; $\mathrm{Tr}(O\rho_\beta)$; the $\ell^2$ operator norm; reason: words outside $A$ have coefficient $0$; standard meanings; no instance changes
--   - encoding: Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ on the site set $\Lambda$ with distinct non-identity strings → coefficient function $c$ on Pauli words of $\Lambda$ with $c(I)=0$, $A=\{P:c_P\neq0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eqs. (40)–(42), p.17; §5.4, eq. (279), p.58

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_Supplement_HasInteractionRange
import Definitions.Def_GeoQAC_IsSupportedOn
import Definitions.Def_QThermalClassical_Supplement_thermalExpect
import Definitions.Def_DistQuantumQuery_traceNorm
import Definitions.Def_QThermalClassical_Supplement_maxCoeff

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 5 (Exponential decay of correlations).** Let `H = Σ_a c_a P_a` be an
`(s, k)`-long-range Pauli Hamiltonian on a finite set of sites `Λ` with distance `d`, with
interaction range `R > 0` (40). Let `A, B` be Hermitian observables supported on disjoint sets
`X, Y ⊂ Λ`. Then for `0 ≤ β ≤ 1/(128e max{s, √(s max_a |c_a| max{k, |X| + |Y|})})` (41),
`|⟨AB⟩_β − ⟨A⟩_β⟨B⟩_β| ≤ 48 · 2^{|X|+|Y|} ‖A‖‖B‖ exp(−(log 8/(6R)) d(X, Y))` (42).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eqs. (40)–(42), p.17; geometric locality and `d(X, Y)` in §5.4,
eq. (279), p.58.

**Formalization Note.** The sites form any finite metric space (the paper's lattice `Λ ⊂ ℤ^D`
with Euclidean distance is one); "geometrically local with interaction range `R`" is (40).
`⟨O⟩_β = Tr(O ρ_β(H))`, `‖·‖` the operator norm (the published `DistQuantumQuery.opNorm`, Mathlib's ℓ² operator norm),
"supported on" the published `GeoQAC.IsSupportedOn` (`A = A_X ⊗ I`), `log` the natural log, `e = exp 1`.
`R > 0` makes `log 8/(6R)` defined (any `R` satisfying (40) may be enlarged). -/
theorem theorem_5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    (s k R : ℝ) (hs : 0 < s) (hk : 0 < k) (hR : 0 < R) (c : PauliWord Λ → ℝ)
    (hc : IsLongRangePauli s k c) (hrange : HasInteractionRange R c)
    (X Y : Finset Λ) (hXY : Disjoint X Y) (A B : Op Λ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAX : GeoQAC.IsSupportedOn X A) (hBY : GeoQAC.IsSupportedOn Y B) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / (128 * Real.exp 1 *
      max s (Real.sqrt (s * maxCoeff c * max k ((X.card + Y.card : ℕ) : ℝ))))) :
    ‖thermalExpect (ham c) β (A * B) - thermalExpect (ham c) β A * thermalExpect (ham c) β B‖ ≤
      48 * 2 ^ (X.card + Y.card) * DistQuantumQuery.opNorm A * DistQuantumQuery.opNorm B *
        Real.exp (-(Real.log 8 / (6 * R)) * setDist X Y) := by sorry

end QThermalClassical.Supplement
