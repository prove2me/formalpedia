-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_maxCutSubgrad_mem_epsSubdiff
-- name    : QAlgorithms.Nannicini.maxCutSubgrad_mem_epsSubdiff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:58.532339+00:00
-- url     : https://prove2.me/theorems/3447d3ba-b673-4f89-936e-bc86c8b5d802
-- title:
--   The estimated MaxCut subgradient is an ϵ/2-subgradient (corrected zero branch)
-- statement:
--   This is Proposition 8.28 of Nannicini, stated with a correction of its zero branch.
--
--   Let $C\in\mathbb R^{n\times n}$ be a nonzero symmetric matrix and $\hat C = C/\|C\|_F$. Let $\gamma\in[-1,1]$, $\epsilon>0$, and for Hermitian $\rho$ let
--
--   $$f_\gamma(\rho)=\max\Big\{\gamma-\operatorname{Tr}(\hat C\rho),\ \sum_{j=1}^n\big|\rho_{jj}-\tfrac1n\big|\Big\}.$$
--
--   Let $\rho$ be a density matrix (the current iterate $\rho^{(t)}$) and let $\widetilde c\in\mathbb R$, $\widetilde d\in\mathbb R^n$ be estimates with $|\widetilde c-\operatorname{Tr}(\hat C\rho)|\le\epsilon/4$ and $\sum_j|\widetilde d_j-\rho_{jj}|\le\epsilon/4$. Put $u=\gamma-\widetilde c$, $v=\sum_j|\widetilde d_j-1/n|$, and let $G$ be the output of the procedure: $G=0$ if $\max\{u,v\}\le 3\epsilon/4$; otherwise $G=-\hat C$ if $u\ge v$; otherwise $G=\sum_j\big(\mathbb 1[\widetilde d_j>1/n]-\mathbb 1[\widetilde d_j<1/n]\big)E_{jj}$. Then
--
--   1. if $\max\{u,v\}\le 3\epsilon/4$, then $G=0$ and $f_\gamma(\rho)\le\epsilon$;
--   2. if $\max\{u,v\}>3\epsilon/4$, then $G\in\partial_{\epsilon/2}f_\gamma(\rho)$, i.e. for every Hermitian matrix $X$,
--
--   $$f_\gamma(X)\ \ge\ f_\gamma(\rho)+\operatorname{Re}\operatorname{Tr}\big(G(X-\rho)^\dagger\big)-\frac{\epsilon}{2}.$$
--
--   The printed proposition claims $G\in\partial_{\epsilon/2}f_\gamma(\rho)$ also in the zero branch; this fails (take $n=2$, $\gamma=-1$, $\rho=\operatorname{diag}(\tfrac12+\tfrac\epsilon2,\tfrac12-\tfrac\epsilon2)$, diagonal estimates $\tfrac12\pm\tfrac{3\epsilon}8$: then $G=0$, $f_\gamma(\rho)=\epsilon$ and $f_\gamma(I/2)=0$). The source itself uses the zero branch only as a certificate that $f_\gamma(\rho)\le\epsilon$.
--
--   The proposition supplies the inexact subgradients for the mirror-descent solver of the MaxCut SDP relaxation.
--
--   **Formalization Note** $C$ is a real matrix embedded entrywise in $\mathbb C^{n\times n}$; subgradients live in the real space of Hermitian matrices with the trace pairing $\langle G,X\rangle=\operatorname{Re}\operatorname{Tr}(GX^\dagger)$, and $\operatorname{Tr}$ and $\rho_{jj}$ enter $f_\gamma$ through their real parts.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 201, Proposition 8.28. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

/-- Nannicini p.201, Proposition 8.28, **corrected** (trap 30). As printed: "Let `G^(t)` be
computed according to the algorithm above. Then `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`."

The zero branch is false as printed: the book's proof only shows that `0` is an `ϵ`-subgradient
(not an `ϵ/2`-subgradient) there. Counterexample: `n = 2`, `γ = −1`,
`ρ = diag(1/2 + ϵ/2, 1/2 − ϵ/2)`, diagonal estimates `1/2 ± 3ϵ/8` and the exact value of
`Tr(Ĉρ)`; the estimated maximum is `3ϵ/4`, so `G = 0`, while `f_γ(ρ) = ϵ` and `f_γ(I/2) = 0`.
The book itself says (p.201) that the zero branch only signals `f_γ(ρ^(t)) ≤ ϵ`. Stated:

1. if the estimated maximum is at most `3ϵ/4`, then `G = 0` and `f_γ(ρ) ≤ ϵ`;
2. otherwise `G ∈ ∂_{ϵ/2} f_γ(ρ)`, the `ϵ/2`-subgradient inequality holding at every Hermitian
   matrix.

The current iterate `ρ^(t)` is any density matrix `ρ`; the estimates satisfy Eq. (8.27). -/
theorem maxCutSubgrad_mem_epsSubdiff {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDensityMatrix ρ) (estC : ℝ) (estD : Fin n → ℝ)
    (hestC : |estC - (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re| ≤ ε * 4⁻¹)
    (hestD : ∑ j, |estD j - (ρ j j).re| ≤ ε * 4⁻¹) :
    (max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ →
        maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD = 0 ∧
          maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρ ≤ ε) ∧
      (3 * ε * 4⁻¹ < max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) →
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) ρ
          (traceRePairing (maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD))) := by
  sorry




















end QAlgorithms.Nannicini
