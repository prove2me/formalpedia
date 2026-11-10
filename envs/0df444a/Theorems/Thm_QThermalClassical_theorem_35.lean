-- Prove2me | Theorems.Thm_QThermalClassical_theorem_35
-- name    : QThermalClassical.theorem_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:52.974205+00:00
-- url     : https://prove2.me/theorems/6cc59dc1-a2d3-4e24-9244-c3fcbcb70075
-- title:
--   Theorem 35 — commuting entangled Hamiltonians (main sentence)
-- statement:
--   Let $\Lambda_L=\{1,\dots,L\}^D$, $m\ge2$, $a\ge0$, and couplings $J_{x,y}=J_{y,x}\ge0$. The Hamiltonian
--   $$
--   H=-a\sum_{x\in\Lambda_L}\sum_{i=1}^mQ_{x,i}-\sum_{x,y\in\Lambda_L}\sum_{i=1}^mJ_{x,y}Q_{x,i}Z_{c_{y,i}}\qquad(408)
--   $$
--   with $Q_{x,i}$ as in (409):
--   1. is a commuting Hamiltonian;
--   2. has locality $2m-1$: every term acts on at most $2m-1$ qubits;
--   3. has an entangled Gibbs state $\rho_\beta(H)$ whenever, for some $x\in\Lambda_L$,
--   $$
--   m\tanh\Big(\beta\big(a+\sum_{y\in\Lambda_L}J_{x,y}\big)\Big)>1 .
--   $$
--
--   With the long-range parameters of the next milestone this gives clause 2 of Theorem 1(a).
--
--   Differences from the source:
--   - reading: "locality $k=2m-1$" → every term has support of size at most $2m-1$; reason: locality is an upper bound (Definition 2.3); with $J=0$ the terms have weight $2m-2$, so an equality would be false
--   - encoding: the lattice $\{1,\dots,L\}^D$, the qubits $q_{x,i,j,\ell}$, $c_{x,i}$, and $H$ → `Fin D → Fin L`, a sum type of qubits, and the coefficient function whose Hamiltonian is (408); reason: relabelling; the operator is (408)
--   - encoding: "entangled" → not in $\mathrm{Sep}_n$ of (7); reason: the paper's definition of entanglement
--   - encoding: inverse temperature $\beta\ge0$ → every real $\beta$; reason: with $a\ge0$ and $J\ge0$ the condition $m\tanh(\beta(a+\sum_yJ_{x,y}))>1$ forces $\beta>0$, so no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, eqs. (408)–(409), p.84

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_IsCommutingPauli
import Definitions.Def_QThermalClassical_ent35Coeff

set_option autoImplicit false

namespace QThermalClassical

/-- **Theorem 35 (Entangled Hamiltonians), main sentence.** On the lattice
`Λ_L = {1, …, L}^D` with `m ≥ 2`, symmetric couplings `J_{x,y} = J_{y,x} ≥ 0` and `a ≥ 0`, the
Hamiltonian (408) `H = −a Σ_x Σ_i Q_{x,i} − Σ_{x,y} Σ_i J_{x,y} Q_{x,i} Z_{c_{y,i}}` is a commuting
Hamiltonian with locality `2m − 1`, and its Gibbs state is entangled if for some `x ∈ Λ_L`,
`m tanh(β(a + Σ_y J_{x,y})) > 1`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, eqs. (408)–(409), p.84.

**Formalization Note.** "Locality `k = 2m − 1`" is read as an upper bound on the support of
every term (the sense of "locality" in Definition 2.3): with `J = 0` the terms have weight
`2m − 2`. "Entangled" is "not fully separable" (not in `Sep_n` of (7)). `β` is any real number
(the condition forces `β > 0`). -/
theorem theorem_35 (D L m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : 0 ≤ a)
    (J : (Fin D → Fin L) → (Fin D → Fin L) → ℝ) (hJsymm : ∀ x y, J x y = J y x)
    (hJnn : ∀ x y, 0 ≤ J x y) :
    IsCommutingPauli (ent35Coeff D L m a J) ∧
    (∀ P, ent35Coeff D L m a J P ≠ 0 → (pauliSupport P).card ≤ 2 * m - 1) ∧
    ∀ β : ℝ, (∃ x, 1 < (m : ℝ) * Real.tanh (β * (a + ∑ y, J x y))) →
      ¬ IsSeparable (gibbs (ham (ent35Coeff D L m a J)) β) := by sorry

end QThermalClassical
