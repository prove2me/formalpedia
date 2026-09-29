-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
-- name    : TwistedUnipotentTerm.exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/845fce63-bec5-5932-a348-1636b9cafbaa
-- title:
--   Unipotent orbital function as a twisted tree walk count
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\xi_L$ be a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ into $\mathbb{C}^\times$, let $v$ be a nonzero prime of $\mathcal{O}_K$ and $w$ a prime of $\mathcal{O}_L$ lying under $v$; write $q=$ `Ideal.absNorm` of $w$. Assume $\xi_L$ is semi-locally trivial at $v$, in the sense that `semiLocalCharacter K L ξL v ζ`, the finite product over all $w'\mid v$ of $\xi_L(\det$ of the Hecke generator at $w'$ attached to the $w'$-component of $\zeta)$, equals $1$ for every $\zeta$ in `integralUnits K L v`, the unit group of the submonoid image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_v}$ in $(L\otimes_K K_v)^\times$. Let $\varpi$ be an irreducible element of the valuation ring of $L_w$ with nonzero image in $L_w$, let $rT:\mathrm{Fin}\,n\to \mathrm{GL}_2(L_w)$ be a Hecke coset system for the image subgroup $\mathrm{GL}_2(\mathcal{O}_w)$ and the element $\mathrm{diag}(\varpi,1)$ — each $rT\,i$ lies in the double coset, the classes $rT\,i\cdot \mathrm{GL}_2(\mathcal{O}_w)$ exhaust it, and $i\mapsto rT\,i\cdot\mathrm{GL}_2(\mathcal{O}_w)$ is injective — and let $z\in \mathrm{GL}_2(L_w)$ have matrix the scalar $\varpi\cdot 1$. Let $W:\mathbb{N}\to\mathbb{N}\to\mathbb{N}$ satisfy $W(0,0)=1$, $W(0,d+1)=0$, $W(k+1,0)=(q+1)W(k,1)$ and $W(k+1,d+1)=W(k,d)+q\,W(k,d+2)$. Then there is $V\in\mathbb{C}$, $V\neq 0$, such that for all $k,j\in\mathbb{N}$ and all $x\in L\otimes_K v$-completion, the value `unipotentOrbitalFn K L ξL v w n rT z k j x` — the integral over $\zeta\in(L\otimes_K K_v)^\times$ against Haar measure of `semiLocalCharacter` at $\zeta$ times the `semiLocalHaar`-integral over $\kappa$ in `semiLocalIntegralSet` of `wordIndicator` applied to $\kappa^{-1}\cdot(\text{central }\zeta)\cdot(\text{unipotent }x)$ — equals $V$ times $\frac{1+(-1)^k}{2}\,\xi_L(\det\,$`heckeGen (𝓞 L) L w.1`$)^{\lfloor k/2\rfloor+j}$ times the indicator, at $x$, of the set of those $x$ whose components under the base-change isomorphism $L\otimes_K K_v\cong\prod_{w'\mid v}L_{w'}$ are integral at every $w'\neq w$, of the function sending $x$ to $W\bigl(k,\,2\,(\mathrm{WithZero.log}\ \mathrm{Valued.v}\,x_w)^{+}\bigr)$ cast to $\mathbb{C}$, where $(\cdot)^{+}$ denotes `toNat` (so the second argument is $2\max(0,-\mathrm{ord}_w x_w)$).
--
--   This is the closed evaluation of the semi-local twisted unipotent orbital function at an unramified place: it identifies it, up to a nonzero constant and a character factor, with the walk counts $W(k,d)$ on the $(q+1)$-regular tree attached to $\mathrm{GL}_2(L_w)$, vanishing for odd $k$. It feeds the computations of the twisted local factor at one and of its derivative, [`TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram`](thm.html#TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram) and [`TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram`](thm.html#TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.exists_ne_zero_forall_unipotentOrbitalFn_eq_mul_indicator_walkCount_of_forall_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
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
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm w.1.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm w.1.asIdeal * W k (d + 2)) :
    ∃ V : ℂ, V ≠ 0 ∧ ∀ (k j : ℕ) (x : L ⊗[K] v.adicCompletion K),
      TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j x =
        V * ((1 + (-1 : ℂ) ^ k) / 2 * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (k / 2 + j)) *
          {x : L ⊗[K] v.adicCompletion K | ∀ w' : v.Extension (𝓞 L), w' ≠ w →
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L}.indicator
            (fun x => (W k (2 * (WithZero.log (Valued.v
              (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) x := by sorry
