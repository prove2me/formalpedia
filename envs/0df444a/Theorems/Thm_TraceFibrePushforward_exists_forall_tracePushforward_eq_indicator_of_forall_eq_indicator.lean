-- Prove2me | Theorems.Thm_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
-- name    : TraceFibrePushforward.exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/b07a8151-bd21-59c6-b0ce-4fb6c8cf1a64
-- title:
--   Trace push-forward of factorisable adelic test functions
-- statement:
--   Let $K \subseteq L$ be number fields (with $L$ a $K$-algebra), and fix measurable and Borel structures on each completion $K_v$, $v$ a nonzero prime of $\mathcal O_K$. The assertion is that there is a finite set $S_0$ of nonzero primes of $\mathcal O_K$ such that for every continuous, compactly supported $g_L \colon \mathbb A_{L,\infty} \to \mathbb C$ on the infinite adeles of $L$ there is a function $g_K$ on the infinite adeles of $K$ with the following property. Let $S_K$ be a finite set of primes of $\mathcal O_K$ containing $S_0$, let $F_v \colon L \otimes_K K_v \to \mathbb C$ be given for each $v$, and let $F \colon \mathbb A_L \to \mathbb C$ be the function sending $x$ to $g_L(x_\infty) \prod_{v \in S_K} F_v(\mathrm{ev}_v(x_{\mathrm{fin}}))$ on the set of adeles whose semi-local component $\mathrm{ev}_v(x_{\mathrm{fin}}) \in L \otimes_K K_v$ lies in the image of $\mathcal O_L \otimes \mathcal O_{K_v}$ for every $v \notin S_K$, and to $0$ elsewhere (here $\mathrm{ev}_v$ is [`AutomorphicForm.semiLocalEval`](def/AutomorphicForm_TwistedOrbital.html#L441), the $v$-semi-local evaluation obtained from the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$). Assume each $F_v$, $v \in S_K$, is locally constant with compact support. Then for every adele $r$ of $K$ the trace push-forward `tracePushforward K L F r` — the integral of $F$ over the trace fibre $\mathbb A_K^{\,\dim_K \ker(\mathrm{Tr}_{L/K})}$-parametrisation $w \mapsto \beta(r)[L:K]^{-1} + \sum_i \beta(w_i) b_i$ against the product adelic Haar measure — equals $g_K(r_\infty) \prod_{v \in S_K} (\mathrm{localTracePushforward}\,F_v)(r_v)$ when $r$ is integral at every $v \notin S_K$, and $0$ otherwise; moreover each local push-forward `localTracePushforward K L v (Fv v)`, given by integrating $F_v$ over $w \mapsto [L:K]^{-1} \otimes r + \sum_i b_i \otimes w_i$ against the Haar measure on $K_v$ normalised so that $\mathcal O_{K_v}$ has volume $1$, is locally constant with compact support for $v \in S_K$. The set $S_0$ is independent of $g_L$, and $g_K$ is independent of $S_K$, of the $F_v$ and of $F$.
--
--   This is the factorisation statement for the push-forward along the trace from $L$ to $K$: a test function on $\mathbb A_L$ which is a product of an archimedean factor, locally constant compactly supported semi-local factors at the places of $S_K$, and the characteristic function of the integers outside $S_K$, has trace push-forward of exactly the same shape on $\mathbb A_K$, with the local factors replaced by their local trace push-forwards. It feeds the computations of twisted orbital integrals and of the local zeta factors attached to twisted unipotent terms, where the global integral must be broken up into a product of local ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.lean

import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct
open scoped TensorProduct.RightActions in

theorem TraceFibrePushforward.exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ gL : InfiniteAdeleRing L → ℂ, Continuous gL → HasCompactSupport gL →
      ∃ gK : InfiniteAdeleRing K → ℂ,
      ∀ (SK : Finset (HeightOneSpectrum (𝓞 K))) (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ)
        (F : AdeleRing (𝓞 L) L → ℂ),
        S₀ ⊆ SK →
        (∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
          (fun x => gL x.1 * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x) →
        (∀ v ∈ SK, IsLocallyConstant (Fv v) ∧ HasCompactSupport (Fv v)) →
        (∀ r, tracePushforward K L F r = (NumberField.TateGlobal.integralOutside SK).indicator
          (fun r => gK r.1 * ∏ v ∈ SK, localTracePushforward K L v (Fv v) ((r.2 : FiniteAdeleRing (𝓞 K) K) v)) r) ∧
          ∀ v ∈ SK, IsLocallyConstant (localTracePushforward K L v (Fv v)) ∧
            HasCompactSupport (localTracePushforward K L v (Fv v)) := by sorry
