-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
-- name    : TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/87f5f6fb-9b2a-55b4-a840-a684c5faadec
-- title:
--   Derivative at s=1 of the twisted local unipotent zeta integral
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idèle Galois descent datum for $L/K$ (a monoid homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of the adèle ring of $L$, compatible with the structure map from $L$ and continuous in each automorphism), let $\sigma$ be a $K$-automorphism of $L$, and let $\xi_L$ be a homomorphism from the full subgroup of the idèle units of $L$ to $\mathbb{C}^{\times}$ whose associated complex-valued function on the idèle units is continuous. Let $v$ be a nonzero prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ lying over it, assume every prime of $\mathcal{O}_L$ over $v$ has ramification index $1$, and assume the semilocal character attached to $\xi_L$ at $v$ — the finite product over the primes above $v$ of $\xi_L$ evaluated at the determinant of the Hecke generator built from the unit component — takes the value $1$ on the subgroup of units coming from $L \otimes_K \mathcal{O}_{K_v}$ via the integral base-change map. Let $\varpi$ be an irreducible element of the valuation ring at $w$ with nonzero image in $L_w$, let $rT \colon \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ be a system of representatives for the double coset of $\mathrm{diag}(\varpi,1)$ under $\mathrm{GL}_2(\mathcal{O}_w)$ (each $rT\,i$ lies in the double coset, every element of the double coset lies in the left coset of some $rT\,i$, and these left cosets are distinct), and let $z \in \mathrm{GL}_2(L_w)$ have matrix $\varpi \cdot 1$. Let $\mu$ be an additive Haar measure on $K_v$ with its Borel structure. Then there are constants $e_1, e_2 \in \mathbb{C}$, independent of $k$ and $j$, such that for all natural numbers $k, j$ the derivative at $s = 1$ of the local zeta integral $s \mapsto \int f_{k,j}(x)\,|x|^{s}$ of the twisted local factor $f_{k,j}$ against the trivial character equals
--   $$e_1\Bigl(1+(-1)^k\Bigr)\bigl(4 N_w \xi_w\bigr)^{\lfloor k/2 \rfloor}\xi_w^{\,j} \;+\; e_2 \frac{1+(-1)^k}{2}\bigl(4 N_w \xi_w\bigr)^{\lfloor k/2 \rfloor}\Bigl(\prod_{n < \lfloor k/2 \rfloor} \frac{2n+1}{2n+2}\Bigr)\xi_w^{\,j},$$
--   where $N_w$ is the absolute norm of $w$ viewed in $\mathbb{C}$ and $\xi_w$ is the value of $\xi_L$ at the determinant of the adelic Hecke generator at $w$; in particular both terms vanish for odd $k$. Here $f_{k,j}$ is the pushforward along the trace fibres over $K_v$ of the unipotent orbital function at $w$ attached to $\xi_L$, $\varpi$, $rT$, $z$ and the profile $(k,j)$; the data $D$ and $\sigma$ are arguments of that local factor but do not enter its value.
--
--   This is the local unipotent term of the comparison of trace formulae at a finite place unramified in $L/K$: the logarithmic derivative at the edge of Tate's local zeta integral of a Hecke-word orbital integral is shown to lie in the two-dimensional span of the doubled edge value and the central-binomial moment, with coefficients depending on the place and the character but not on the word profile $(k,j)$. It is used in the global statement [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hunr : ∀ w₂ : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w₂ = v →
      (HeightOneSpectrum.under (𝓞 K) w₂).asIdeal.ramificationIdx' w₂.asIdeal = 1)
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    ∃ e₁ e₂ : ℂ, ∀ k j : ℕ,
      deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta μ (twistedLocalFactor K L D σ ξL v w n rT z k j) 1 s) 1 =
        e₁ * ((1 + (-1 : ℂ) ^ k) * (4 * (AutomorphicForm.HeckeEigensystem.cNorm w.1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) +
        e₂ * ((1 + (-1 : ℂ) ^ k) / 2 * (4 * (AutomorphicForm.HeckeEigensystem.cNorm w.1 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (k / 2) *
            ((∏ n ∈ Finset.range (k / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ j) := by sorry
