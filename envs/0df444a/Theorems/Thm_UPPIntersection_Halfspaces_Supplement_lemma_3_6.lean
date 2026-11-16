-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_lemma_3_6
-- name    : UPPIntersection.Halfspaces.Supplement.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:05.038594+00:00
-- url     : https://prove2.me/theorems/50588848-87fd-441e-a985-9cc591654550
-- title:
--   Lemma 3.6 — $D_s$-correlation of tensor basis elements $\Psi_J,\Psi_{J'}$
-- statement:
--   Let $d\ge2$ and $k\ge0$. Let $p_0,p_1,\dots$ be a degree-ordered orthonormal polynomial basis of $L^2(S^{d-1})$ (as obtained by Gram–Schmidt on the monomials in nondecreasing order of total degree), and for $J=(j_1,\dots,j_k)$ let $\Psi_J(x_1,\dots,x_k)=\prod_ip_{j_i}(x_i)$. Let $J,J'\in\{0,1,2,\dots\}^k$, $s\in[-1,1]^k$, and $\ell_i=\deg(p_{j_i})$. Then
--   $$\mathbb E_{(X,Y)\sim D_s}\big[\Psi_J(X)\Psi_{J'}(Y)\big]=\begin{cases}\prod_{i=1}^kG^d_{\ell_i}(s_i)&\text{if }J=J',\\[2pt]0&\text{if }J\neq J'.\end{cases}$$
--   Here $D_s$ is the experiment of §3: $X_1,\dots,X_k$ independent uniform on $S^{d-1}$, $V_i$ independent uniform on the great subsphere orthogonal to $X_i$, and $Y_i=s_iX_i+\sqrt{1-s_i^2}\,V_i$.
--
--   This is the diagonalization step of §3.2: the symmetrization of two tensor basis elements is a product of Gegenbauer polynomials, which turns $H_{f,g}$ into the series of Theorem 3.7.
--
--   Differences from the source:
--   - encoding: G^d_i defined as the unique degree-i polynomials orthogonal for v_d(t)=(1−t²)^((d−3)/2) on [−1,1] with G^d_i(1)=1 (Definition 3.3) → the published SphereSOS.Rate.geg, defined by G_0=1, G_1=t and (k+d−1)G_{k+2}=(2k+d)tG_{k+1}−(k+1)G_k; reason: this recurrence defines the same normalized Gegenbauer polynomials for every d ≥ 2 (Chebyshev polynomials at d=2); the identification is a fact to be used, not an assumption
--   - generalization: the specific basis obtained by Gram–Schmidt on monomials in nondecreasing order of total degree → every degree-ordered orthonormal polynomial basis (polynomial of degree ≤ ℓ(j), orthogonal to lower degree, orthonormal, spanning, ℓ nondecreasing); reason: the paper's Gram–Schmidt basis has all these properties, with ℓ(j) = deg p_j, so the statement specializes to it
--   - encoding: ℓ_i = deg(p_{j_i}) → the degree label ℓ(j_i) of the basis; reason: for a basis with these properties the label is the exact degree: a nonzero p_j orthogonal to all polynomials of degree < ℓ(j) cannot have lower degree
--   - encoding: V_i uniform on the orthogonal complement of X_i in S^{d−1} → the normalized projection of an independent uniform point onto X_i^⊥, as in the published symH experiment; reason: this is the uniform law on the great subsphere; the projection is undefined only on a null set
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 18, Lemma 3.6 (with the basis p_j and Ψ_J defined at the start of §3.2, p. 18); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_SphereSOS_Rate_Gegenbauer
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open MeasureTheory

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Lemma 3.6 (p. 18). Let `p₀, p₁, …` be a degree-ordered orthonormal polynomial
basis of `L²(S^{d-1})` with degree labels `deg`, and `Ψ_J(x) = ∏_i p_{j_i}(x_i)`. For all
`J, J' ∈ ℕ^k` and `s ∈ [-1,1]^k`, the expectation of `Ψ_J(X) Ψ_{J'}(Y)` under the experiment `D_s`
equals `∏_i G^d_{ℓ_i}(s_i)` with `ℓ_i = deg(j_i)` if `J = J'`, and `0` otherwise. -/
theorem lemma_3_6 (d k : ℕ) (hd : 2 ≤ d) (p : ℕ → Sph d → ℝ) (deg : ℕ → ℕ)
    (hp : IsDegreeOrderedONB d p deg) (J J' : Fin k → ℕ)
    (s : Fin k → ℝ) (hs : s ∈ Set.Icc (fun _ => -1) (fun _ => 1)) :
    ∫ q : (Fin k → Sph d) × (Fin k → Sph d),
        psi p J q.1 * psi p J' (fun i => partner (s i) (q.1 i) (q.2 i))
        ∂((sphereLawPow d k).prod (sphereLawPow d k)) =
      if J = J' then gegProd d (fun i => deg (J i)) s else 0 := by sorry

end UPPIntersection.Halfspaces.Supplement
