-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/080d0e93-ea02-57e8-a8c1-25ad3007022c
-- title:
--   Strong approximation for Eichler orders away from one prime
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime with $q'\ge 5$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsDefiniteRamifiedExactlyAt`, i.e. $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q'\in v$. Let $N$ be a nonzero squarefree natural number, let $\Lambda$ be a maximal order (a $\mathbb{Z}$-submodule containing $1$, closed under multiplication, $\mathbb{Q}$-spanning the algebra and finitely generated, maximal among such) and let $R\le\Lambda$ be an Eichler order of level $N$, i.e. an intersection $R=\Lambda_1\cap\Lambda_2$ of two maximal orders with relative index $N$ of $R$ in $\Lambda_1$. Let $r$ be a prime with $r\ne q'$ and $r\nmid N$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ containing $r$. Then every unit $x$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ factors as $x=\mathrm{diag}(\gamma)\,g\,u$ with $\gamma\in\mathbb{H}[\mathbb{Q},a,b]^\times$ embedded diagonally, $u$ in the stabiliser of the adelic box of $R$, and $g$ whose component at every prime $w\ne v$ equals $1$.
--
--   This is strong approximation for the unit group of an Eichler order of squarefree level in a definite quaternion algebra over $\mathbb{Q}$, in the form $\widehat{\mathbb{H}}^\times=\mathbb{H}^\times\cdot\mathbb{H}_v^\times\cdot\widehat{R}^\times$, equivalently the connectedness of the $r$-Brandt graph of $R$. It feeds the identification of the vertex and edge quotients of the Čerednik–Drinfeld coset graph with class sets, and the unconditional form of the same decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] (hN : Squarefree N)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ (γ : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer R ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g * u := by sorry
