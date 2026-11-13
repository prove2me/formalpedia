-- Prove2me | Theorems.Thm_PhaseEncodedQGE_corollary_A_19
-- name    : PhaseEncodedQGE.corollary_A_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:44.412203+00:00
-- url     : https://prove2.me/theorems/21f52437-d3d2-46e3-a887-61f30eb59456
-- title:
--   Corollary A.19 — complementarity: X1 reads the even, Y1 the odd readings, together the profile
-- statement:
--   For the single-repetition members:
--
--   1. $h^{X,1}(k)=\cos(\gamma(2k-3))$ is even and $h^{Y,1}(k)=\sin(\gamma(2k-3))$ is odd under $k\mapsto3-k$ ($0\le k\le3$);
--   2. on a layer (equal $|D|$, same $n$) the PE-X1 value of an outcome is a function of the even readings $(E_{\mathrm{in}},E_{\mathrm{out}})$ of its profile;
--   3. the PE-Y1 value is a function of the odd readings $(q_3-q_0,\,q_2-q_1)^{\mathrm{in}}$, $(q_3-q_0,\,q_2-q_1)^{\mathrm{out}}$;
--   4. given $|D|$ and $n$, the even and odd readings together determine the profile: for either count vector, $q_0+q_3$, $q_1+q_2$, $q_3-q_0$, $q_2-q_1$ are four independent linear forms in $(q_0,\dots,q_3)$, i.e.
--   $$\det\begin{pmatrix}1&0&0&1\\0&1&1&0\\-1&0&0&1\\0&-1&1&0\end{pmatrix}\ne0 .$$
--
--   Graphs are cubic with the degree-aware preparation and $\cos(\eta/2)\ne0\ne\sin(\eta/2)$; "function of" means equal readings give equal values, for outcomes of two cubic graphs on the same vertex set.
--
--   Differences from the source:
--   - reading: the PE-X1 value of an outcome is a function of the even readings $(E_{\mathrm{in}},E_{\mathrm{out}})$ → equal $(E_{\mathrm{in}},E_{\mathrm{out}})$ and equal $|D|$ (same $n$) give equal PE-X1 values; reason: by (11)/(27) the X value also involves |D| and n, which the corollary's next sentence fixes ('Given |D| and n'); without them the claim is not meant
--   - generalization: outcomes of the layer of one graph G → outcomes of the layers of two cubic graphs G, G′ on the same n vertices; reason: taking G′ = G gives the paper's statement; the first-order value depends only on the profile, so the paper's argument is graph-independent
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
--   - encoding: four independent linear forms → the determinant of their coefficient matrix is nonzero; reason: linear independence of four forms in four variables
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.6, p.21 (PDF p.22), Corollary A.19

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Corollary A.19, complementarity (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.6, p.21).

For the single-repetition members, `h^{X,1}(k) = cos(γ(2k − 3))` is even and
`h^{Y,1}(k) = sin(γ(2k − 3))` is odd under `k ↦ 3 − k`. Consequently the PE-X1 value of an outcome
is a function of the even readings `(E_in, E_out)` of its profile and the PE-Y1 value a function of
the odd readings `(q_3 − q_0, q_2 − q_1)^in`, `(q_3 − q_0, q_2 − q_1)^out`. Given `|D|` and `n`, the
even and odd readings together determine the profile (18): for either count vector, `q_0 + q_3`,
`q_1 + q_2` and `q_3 − q_0`, `q_2 − q_1` are four independent linear forms in `(q_0, …, q_3)`.

**Formalization Note** "A function of" is stated as: equal readings (and, for the X value, equal
`|D|` on the same `n`, as in (27)) give equal values, across two cubic graphs on `Fin n` and the
degree-aware preparation with `cos(η/2) ≠ 0 ≠ sin(η/2)`. The independence of the four forms is the
nonvanishing of the determinant of their coefficient matrix. -/
theorem corollary_A_19 (γ : ℝ) :
    (∀ k : ℕ, k ≤ 3 → hX 1 γ (3 - k) = hX 1 γ k ∧ hY γ (3 - k) = -hY γ k) ∧
    (∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), IsCubic G → IsCubic G' → ∀ (η : ℝ),
      Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 → ∀ x x' : Outcome n,
        (defects x).card = (defects x').card →
        Ein G (defects x) = Ein G' (defects x') → Eout G (defects x) = Eout G' (defects x') →
        firstOrder (degPrep G η) .X 1 G γ x = firstOrder (degPrep G' η) .X 1 G' γ x') ∧
    (∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), IsCubic G → IsCubic G' → ∀ (η : ℝ),
      Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 → ∀ x x' : Outcome n,
        oddIn G (defects x) = oddIn G' (defects x') → oddOut G (defects x) = oddOut G' (defects x') →
        firstOrder (degPrep G η) .Y 1 G γ x = firstOrder (degPrep G' η) .Y 1 G' γ x') ∧
    (∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), IsCubic G → IsCubic G' → ∀ D D' : Finset (Fin n),
      D.card = D'.card → Ein G D = Ein G' D' → Eout G D = Eout G' D' →
      oddIn G D = oddIn G' D' → oddOut G D = oddOut G' D' → profile G D = profile G' D') ∧
    Matrix.det !![(1 : ℚ), 0, 0, 1; 0, 1, 1, 0; -1, 0, 0, 1; 0, -1, 1, 0] ≠ 0 := by sorry

end PhaseEncodedQGE
