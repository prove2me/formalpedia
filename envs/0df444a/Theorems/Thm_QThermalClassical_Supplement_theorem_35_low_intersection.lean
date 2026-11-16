-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_35_low_intersection
-- name    : QThermalClassical.Supplement.theorem_35_low_intersection
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:42:22.356125+00:00
-- url     : https://prove2.me/theorems/80123e91-c47a-4193-88b7-4a9e75b8c938
-- title:
--   Theorem 35, low-intersection bullet — a commuting $(3L^D-2,3)$-low-intersection Hamiltonian entangled for $\beta>96\log2/(\mathfrak d+2)$, at trace distance $\ge1/12$
-- statement:
--   Fix a dimension $D\ge1$ and set $m=2$, $a=0$, $J_{x,y}=1$ (all ordered pairs $x,y$) in the Hamiltonian (408) on $\Lambda_L=\{1,\dots,L\}^D$. Then:
--
--   1. for every $L\ge1$ it is a $(\mathfrak d,3)$-low-intersection Pauli Hamiltonian whose dual degree is exactly $\mathfrak d=3L^D-2$;
--   2. there is $L_0$ such that for every $L\ge L_0$ and every
--   $$
--   \beta>\frac{96\log2}{\mathfrak d+2},\tag{411}
--   $$
--   the Gibbs state is entangled and $\tfrac12\|\rho_\beta-\sigma\|_1\ge\tfrac1{12}$ for every separable state $\sigma$;
--   3. the threshold is $\Theta(1/\mathfrak d)$: there are $C_1,C_2>0$ with $C_1/\mathfrak d\le\frac{96\log2}{\mathfrak d+2}\le C_2/\mathfrak d$ for $\mathfrak d=3L^D-2$, every $D\ge1$ and $L\ge1$.
--
--   This family is the converse of Theorem 1(b).
--
--   Differences from the source:
--   - reading: results in a $(\mathfrak d,3)$-low-intersection Pauli Hamiltonian with $\mathfrak d=3L^D-2$ → for every $L\ge1$: dual degree exactly $3L^D-2$, and $(3L^D-2,3)$-low-intersection; reason: 'with $\mathfrak d=$' names the dual degree (the proof computes it exactly); $L\ge1$ because $\Lambda_0$ is empty
--   - reading: for all $\beta>\dots$ and sufficiently large $L$ → $\exists L_0,\ \forall L\ge L_0,\ \forall\beta>96\log2/(\mathfrak d+2)$ ($L_0$ independent of $\beta$); reason: the stronger of the two orders
--   - encoding: $D$-dimensional lattice; $=\Theta(1/\mathfrak d)$; trace distance; $\log$ → $D\ge1$; explicit constants over $\mathfrak d=3L^D-2$; $\tfrac12\|\cdot\|_1$; natural log; reason: standard meanings; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, low-intersection bullet, eq. (411), p.84

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_ent35Coeff
import Definitions.Def_QThermalClassical_Supplement_IsLowIntersectionPauli
import Definitions.Def_DistQuantumQuery_traceNorm

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 35, low-intersection bullet.** For every dimension `D ≥ 1`, setting `m = 2`,
`a = 0`, `J_{x,y} = 1` in (408):
1. for every `L ≥ 1` the Hamiltonian is a `(d, 3)`-low-intersection Pauli Hamiltonian whose dual
   degree is exactly `d = 3L^D − 2`;
2. for all sufficiently large `L` and all `β > 96 log 2/(d + 2)` (411), the Gibbs state is
   entangled and has trace distance at least `1/12` from every separable state;
3. `96 log 2/(d + 2) = Θ(1/d)`: there are `C₁, C₂ > 0` with
   `C₁/d ≤ 96 log 2/(d + 2) ≤ C₂/d` for `d = 3L^D − 2`, every `L ≥ 1`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, low-intersection bullet, eq. (411), p.84.

**Formalization Note.** The Hamiltonian is the published `ent35Coeff D L 2 0 1`; the double sum
of (408) runs over ordered pairs `x, y`, including `x = y`. "Sufficiently large `L`" is
`∃ L₀, ∀ L ≥ L₀`, `L₀` independent of `β`. The trace distance is `½‖ρ − σ‖₁`, with `‖·‖₁` the published `DistQuantumQuery.traceNorm` (sum of singular values;
its `Fintype` instance on basis strings is passed explicitly); `log` is the
natural log. -/
theorem theorem_35_low_intersection :
    (∀ D : ℕ, 1 ≤ D → ∀ L : ℕ, 1 ≤ L →
      ((dualDegree (ent35Coeff D L 2 0 (fun _ _ => 1)) : ℕ) : ℝ) = 3 * (L : ℝ) ^ D - 2 ∧
      IsLowIntersectionPauli (3 * (L : ℝ) ^ D - 2) 3 (ent35Coeff D L 2 0 (fun _ _ => 1))) ∧
    (∀ D : ℕ, 1 ≤ D → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ β : ℝ,
      96 * Real.log 2 / ((3 * (L : ℝ) ^ D - 2) + 2) < β →
        ¬ IsSeparable (gibbs (ham (ent35Coeff D L 2 0 (fun _ _ => 1))) β) ∧
        ∀ σ : Op (Ent35Qubit D L 2), IsSeparable σ →
          1 / 12 ≤ @DistQuantumQuery.traceNorm (Ent35Qubit D L 2 → Bool) Pi.instFintype _ (gibbs (ham (ent35Coeff D L 2 0 (fun _ _ => 1))) β - σ) / 2) ∧
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ D : ℕ, 1 ≤ D → ∀ L : ℕ, 1 ≤ L →
      C₁ / (3 * (L : ℝ) ^ D - 2) ≤ 96 * Real.log 2 / ((3 * (L : ℝ) ^ D - 2) + 2) ∧
      96 * Real.log 2 / ((3 * (L : ℝ) ^ D - 2) + 2) ≤ C₂ / (3 * (L : ℝ) ^ D - 2)) := by sorry

end QThermalClassical.Supplement
