-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_35_long_range_trace
-- name    : QThermalClassical.Supplement.theorem_35_long_range_trace
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:41:47.391688+00:00
-- url     : https://prove2.me/theorems/a59b9749-0472-49a6-bfac-f6645945d637
-- title:
--   Theorem 35, long-range bullet (second sentence) — for $\beta\ge(2/s)\,\mathrm{artanh}(3/(2m))=\Theta(1/sk)$ and large $L$ the Gibbs state is entangled, at trace distance $\ge1/2$ from $\mathrm{Sep}_n$
-- statement:
--   Fix a dimension $D\ge1$, an integer $k\ge2$ and $s>0$, and set $m=\lfloor k/2\rfloor+1$, $a=s/2$, $J_{x,y}=0$ in the Hamiltonian (408) on the lattice $\Lambda_L=\{1,\dots,L\}^D$. Then:
--
--   1. there is $L_0$ such that for every $L\ge L_0$ and every
--   $$
--   \beta\ge\frac2s\,\mathrm{artanh}\frac{3}{2m},\tag{410}
--   $$
--   the Gibbs state $\rho_\beta$ is entangled and $\tfrac12\|\rho_\beta-\sigma\|_1\ge\tfrac12$ for every separable state $\sigma$;
--   2. the threshold is $\Theta(1/sk)$: there are $C_1,C_2>0$ with $C_1/(sk)\le\frac2s\mathrm{artanh}\frac3{2m}\le C_2/(sk)$ for all $s>0$ and integers $k\ge2$.
--
--   This is the constant-trace-distance form of the converse of Theorem 1(a), used for the lower bound in Theorem 2.
--
--   Differences from the source:
--   - reading: for all $\beta\ge\dots$ and sufficiently large $L$ → $\exists L_0,\ \forall L\ge L_0,\ \forall\beta\ge\frac2s\mathrm{artanh}\frac3{2m}$ ($L_0$ independent of $\beta$); reason: the stronger of the two orders; the proof's condition $L^D\ge64m^2$ does not involve $\beta$
--   - encoding: $D$-dimensional lattice $\{1,\dots,L\}^D$; $k$; $=\Theta(1/sk)$ → $D\ge1$, `Fin D → Fin L`; $k\in\mathbb N$; explicit constants $C_1,C_2$; reason: a $0$-dimensional lattice does not grow with $L$; $\lfloor k/2\rfloor$ is natural-number division; the standard meaning of $\Theta$
--   - encoding: trace distance; separable state → $\tfrac12\|\cdot\|_1$ (sum of singular values); $\mathrm{Sep}_n$ of (7); reason: standard meanings; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, long-range bullet, eq. (410), p.84

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_ent35Coeff
import Definitions.Def_DistQuantumQuery_traceNorm

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 35, long-range bullet, second sentence.** For every dimension `D ≥ 1`, integer
`k ≥ 2` and `s > 0`, with `m = ⌊k/2⌋ + 1`, `a = s/2`, `J = 0` in (408): for all sufficiently
large `L` and all `β ≥ (2/s) artanh(3/(2m))` (410), the Gibbs state is entangled and has trace
distance at least `1/2` from every separable state. Moreover `(2/s) artanh(3/(2m)) = Θ(1/(sk))`:
there are `C₁, C₂ > 0` with `C₁/(sk) ≤ (2/s) artanh(3/(2m)) ≤ C₂/(sk)` for all `s > 0`, `k ≥ 2`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, long-range bullet, eq. (410), p.84.

**Formalization Note.** The Hamiltonian is the published `ent35Coeff D L (k/2+1) (s/2) 0`
(`k/2` is natural-number division, `⌊k/2⌋`). "Sufficiently large `L`" is `∃ L₀, ∀ L ≥ L₀`,
with `L₀` independent of `β`. The trace distance is `½‖ρ − σ‖₁`, with `‖·‖₁` the published `DistQuantumQuery.traceNorm` (sum of singular values;
its `Fintype` instance on basis strings is passed explicitly); "separable" is `Sep_n` of (7).
The lattice `{1, …, L}^D` needs `D ≥ 1` to grow with `L`. `3/(2m) ≤ 3/4` lies in the domain of
`artanh`. -/
theorem theorem_35_long_range_trace :
    (∀ D : ℕ, 1 ≤ D → ∀ k : ℕ, 2 ≤ k → ∀ s : ℝ, 0 < s →
      ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ β : ℝ,
        2 / s * Real.artanh (3 / (2 * ((k / 2 + 1 : ℕ) : ℝ))) ≤ β →
          ¬ IsSeparable (gibbs (ham (ent35Coeff D L (k / 2 + 1) (s / 2) (fun _ _ => 0))) β) ∧
          ∀ σ : Op (Ent35Qubit D L (k / 2 + 1)), IsSeparable σ →
            1 / 2 ≤ @DistQuantumQuery.traceNorm (Ent35Qubit D L (k / 2 + 1) → Bool) Pi.instFintype _
              (gibbs (ham (ent35Coeff D L (k / 2 + 1) (s / 2) (fun _ _ => 0))) β - σ) / 2) ∧
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ s : ℝ, 0 < s → ∀ k : ℕ, 2 ≤ k →
      C₁ / (s * k) ≤ 2 / s * Real.artanh (3 / (2 * ((k / 2 + 1 : ℕ) : ℝ))) ∧
      2 / s * Real.artanh (3 / (2 * ((k / 2 + 1 : ℕ) : ℝ))) ≤ C₂ / (s * k)) := by sorry

end QThermalClassical.Supplement
