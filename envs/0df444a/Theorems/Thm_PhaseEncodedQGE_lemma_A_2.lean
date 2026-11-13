-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_A_2
-- name    : PhaseEncodedQGE.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:21.90271+00:00
-- url     : https://prove2.me/theorems/47c2a6a1-0b35-4087-8c6e-c38892b74f5b
-- title:
--   Lemma A.2 — repetition ratios $R^{(b)}_i(x)=-iz_it^{z_i}\exp(ib\gamma z_iS_i(x))$
-- statement:
--   Let $G$ be a cubic graph with the degree-aware ($R_X$) preparation, $t=\tan(\eta/2)$, $S_i(x)=\sum_{v\in N(i)}z_v$, and let $\phi^{(b)}=E^b\phi_{\mathrm{prep}}$ and $\phi=E^r\phi_{\mathrm{prep}}$. For every vertex $i$, every outcome $x$ and every $b=1,\dots,r$,
--   $$\frac{(E^{r-b}X_i\,\phi^{(b)})(x)}{\phi(x)}=R^{(b)}_i(x):=-i\,z_i\,t^{z_i}\exp\bigl(ib\gamma z_iS_i(x)\bigr).$$
--   In particular $R^{(1)}_i$ is the flip ratio $R_i=\phi(x\oplus e_i)/\phi(x)$ of Lemma B.3 (one edge-phase layer).
--
--   Together with Lemma A.1 this turns the X-mixer first-order term at $r$ tied repetitions into a sum of local ratios.
--
--   Differences from the source:
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
--   - encoding: $R^{(1)}_i=R_i$ of Lemma B.3 → the $b=1$ expression equals the one-layer flip ratio $\phi(x\oplus e_i)/\phi(x)$; reason: R_i of Lemma B.3 is that ratio
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.1, p.14 (PDF p.15), Lemma A.2, eq. (21)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma A.2, the repetition ratios (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.1, p.14, eq. (21)).

For the `R_X` preparation on a cubic graph, with `ϕ^{(b)} = E^b ϕ_prep`, `ϕ = E^r ϕ_prep` and `x`
fixed, `(E^{r−b} X_i ϕ^{(b)})(x) / ϕ(x) = R^{(b)}_i(x) := −i z_i t^{z_i} exp(ibγ z_i S_i(x))` for
`b = 1, …, r`, where `S_i(x) = ∑_{v∈N(i)} z_v`. In particular `R^{(1)}_i = R_i` of Lemma B.3.

**Formalization Note** `X_i` is `site (pauli .X) i`; the second conjunct says that the `b = 1`
expression is the one-layer flip ratio `ϕ(x ⊕ e_i)/ϕ(x)` of Lemma B.3. `c ≠ 0 ≠ s` as in Lemma B.3. -/
theorem lemma_A_2 (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCubic G) (η γ : ℝ)
    (hc : Real.cos (η / 2) ≠ 0) (hs : Real.sin (η / 2) ≠ 0) (r : ℕ) (i : Fin n) (x : Outcome n) :
    (∀ b ∈ Finset.Icc 1 r,
      ((edgeMat G γ ^ (r - b) * site (pauli .X) i) *ᵥ (edgeMat G γ ^ b *ᵥ degPrep G η)) x /
          preMixer (degPrep G η) r G γ x =
        -Complex.I * (spin x i : ℂ) * (Real.tan (η / 2) : ℂ) ^ (spin x i) *
          Complex.exp (Complex.I * (b : ℂ) * γ * (spin x i : ℂ) * (spinSum G x i : ℂ))) ∧
    -Complex.I * (spin x i : ℂ) * (Real.tan (η / 2) : ℂ) ^ (spin x i) *
        Complex.exp (Complex.I * ((1 : ℕ) : ℂ) * γ * (spin x i : ℂ) * (spinSum G x i : ℂ)) =
      preMixer (degPrep G η) 1 G γ (flip x i) / preMixer (degPrep G η) 1 G γ x := by sorry

end PhaseEncodedQGE
