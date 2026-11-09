-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_eq_2_4
-- name    : QuarticGauss390.EigenBound.eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:23.037558+00:00
-- url     : https://prove2.me/theorems/dfd13f03-6ca1-4737-96af-224f56f959d8
-- title:
--   eq. (2.4) — energy of $H_A$ is $\mathrm{Tr}[A M^\rho]$, $M^\rho$ has unit diagonal, $\tau[H_A]=\mathrm{Tr}[A]$
-- statement:
--   Let $c_1,\dots,c_{2n}$ be Majorana operators on the $2^n$-dimensional space $\mathcal H$ ($n\ge2$), let $E$ be the set of pairs $i<j$, $q_p=i\,c_ic_j$, $H_A=\sum_{p,r}A_{pr}q_pq_r$ for a real symmetric $E\times E$ matrix $A$, and $M^\rho=(\operatorname{Re}\operatorname{Tr}[\rho q_pq_r])_{p,r}$ the quartic moment matrix of a density matrix $\rho$. Then:
--
--   1. $M^\rho_{pp}=1$ for every $p\in E$;
--   2. for every density matrix $\rho$ and real symmetric $A$,
--   $$\langle H_A\rangle_\rho=\operatorname{Tr}[AM^\rho];$$
--   3. $\tau[H_A]=\operatorname{Tr}[A]$, where $\tau=2^{-n}\operatorname{Tr}$.
--
--   This duality between coefficient matrices and moment matrices turns energies into linear functionals of the moment matrix; every later bound uses it.
--
--   Differences from the source:
--   - encoding: $\langle H_A\rangle_\rho$ (a real number) → the complex trace $\operatorname{Tr}[\rho H_A]$ equated with the real number $\operatorname{Tr}[AM^\rho]$; reason: the source's identity states the same equality, including that the left side is real
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.7, eq. (2.4) and the sentences around it

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix
open scoped ComplexOrder

namespace QuarticGauss390.EigenBound

/-- eq. (2.4), p.7: for a density matrix `ρ`, `M^ρ` has unit diagonal; `⟨H_A⟩_ρ = Tr[A M^ρ]`
for every real symmetric `A`; and `τ[H_A] = Tr[A]`. -/
theorem eq_2_4 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) :
    (∀ ρ : Op n, IsDensity ρ → ∀ p : Pair n, momentMatrix C ρ p p = 1) ∧
    (∀ ρ : Op n, IsDensity ρ → ∀ A : Matrix (Pair n) (Pair n) ℝ, A.IsSymm →
      expect ρ (coefHam C A) = (((A * momentMatrix C ρ).trace : ℝ) : ℂ)) ∧
    (∀ A : Matrix (Pair n) (Pair n) ℝ, A.IsSymm →
      normTrace n (coefHam C A) = ((A.trace : ℝ) : ℂ)) := by sorry

end QuarticGauss390.EigenBound
