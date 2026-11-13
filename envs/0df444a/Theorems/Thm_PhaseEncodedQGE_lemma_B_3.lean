-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_B_3
-- name    : PhaseEncodedQGE.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:30.613444+00:00
-- url     : https://prove2.me/theorems/5d01576c-8800-4d70-bdac-45706ed44cb1
-- title:
--   Lemma B.3 (= Lemma 3.1) — the flip ratio $R_i(x)=-iz_it^{z_i}\exp(i\gamma z_i\sum_{v\in N(i)}z_v)$
-- statement:
--   Let $G$ be a cubic graph with the degree-aware preparation, $c=\cos(\eta/2)$, $s=\sin(\eta/2)$, $t=s/c$, and let
--   $$\phi(x)=\Bigl[\prod_v a(x_v)\Bigr]\exp\Bigl[-\tfrac{i\gamma}{2}\sum_{uv\in E}z_uz_v\Bigr],\qquad a(0)=c,\ a(1)=-is,$$
--   be the pre-mixer amplitude with one edge-phase layer. For every vertex $i$ and every outcome $x$, the flip ratio $R_i(x)=\phi(x\oplus e_i)/\phi(x)$ is
--   $$R_i(x)=-i\,z_i\,t^{z_i}\exp\Bigl(i\gamma z_i\sum_{v\in N(i)}z_v\Bigr).$$
--
--   The ratio depends only on the spin of $i$ and the spins of its neighbours; it is the local fact from which the first-order template is derived.
--
--   Differences from the source:
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. B.2.2, p.29 (PDF p.30), Lemma B.3, eq. (50) (= Lemma 3.1, §3.1, p.6)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma B.3 (= Lemma 3.1), the flip ratio (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. B.2.2, p.29, eq. (50); §3.1, p.6).

Let `G` be a cubic graph with the degree-aware preparation (every vertex receives `R_X(η)`), let
`ϕ(x) = [∏_v a(x_v)] exp[−(iγ/2) ∑_{uv∈E} z_u z_v]` be the pre-mixer amplitude with one edge-phase
layer, and `R_i(x) = ϕ(x ⊕ e_i)/ϕ(x)`. For every vertex `i` and every `x`,
`R_i(x) = −i z_i t^{z_i} exp(iγ z_i ∑_{v∈N(i)} z_v)` with `t = tan(η/2)`.

**Formalization Note** `ϕ` is `preMixer (degPrep G η) 1 G γ`. The hypotheses `cos(η/2) ≠ 0` and
`sin(η/2) ≠ 0` exclude exactly the angles at which `ϕ` has zeros and `t^{±1}` is undefined.
`t^{z_i}` is an integer power (`z_i = ±1`). -/
theorem lemma_B_3 (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCubic G) (η γ : ℝ)
    (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0) (i : Fin n) (x : Outcome n) :
    preMixer (degPrep G η) 1 G γ (flip x i) / preMixer (degPrep G η) 1 G γ x =
      -Complex.I * (spin x i : ℂ) * (Real.tan (η / 2) : ℂ) ^ (spin x i) *
        Complex.exp (Complex.I * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) := by sorry

end PhaseEncodedQGE
