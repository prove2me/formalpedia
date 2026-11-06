-- Prove2me | Theorems.Thm_TransvectionMixing_corollary_3_4_conditional_mixing_from_rational_section
-- name    : TransvectionMixing.corollary_3_4_conditional_mixing_from_rational_section
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:39.492753+00:00
-- url     : https://prove2.me/theorems/d6764177-dd8b-4caa-8a05-6e2dfdf60fce
-- title:
--   Corollary 3.4 — conditional mixing from a rational section: TV $\le\varepsilon/8$ when $q\ge Q_{\mathrm{geom}}(H,\dim Y;\varepsilon)$
-- statement:
--   Let $Y=\mathbb A^m$ with $m\ge 1$, or $Y=\mathrm{SL}_n$, and let $F:\mathbb A^T\to Y$ be a polynomial map over $\mathbb F_q$ with a rational section over $\mathbb F_q$ and coordinate degrees at most $H\ge 2$. For $0<\varepsilon\le 1/4$, if
--   $$
--   q\ \ge\ Q_{\mathrm{geom}}(H,\dim Y;\varepsilon)=256\,\varepsilon^{-4}H^{13\dim Y/3},
--   $$
--   then $F$ sends uniform coefficients to a law within $\varepsilon/8$ of the uniform law $\pi_Y$ on $Y(\mathbb F_q)$ in total variation:
--   $$
--   \bigl\|F_*\mathrm{Unif}(\mathbb F_q^T)-\pi_Y\bigr\|_{TV}\le\varepsilon/8 .
--   $$
--   Here $\dim\mathbb A^m=m$ and $\dim\mathrm{SL}_n=n^2-1$.
--
--   Every mixing bound of the paper reduces, conditional on the skeleton, to this statement.
--
--   **Formalization Note** A polynomial map to $\mathrm{SL}_n$ is a matrix of polynomials with determinant $1$; "coordinate degrees at most $H$" bounds the total degree of every coordinate (every matrix entry). The rational section is an identity in the function field of $Y$ over $\mathbb F_q$.
--
--   Differences from the source:
--   - encoding: rational section over 𝔽_q (rational functions on a nonempty open subset of Y with F ∘ s = id) → `HasRationalSectionAff` / `HasRationalSectionSL`: a tuple in the function field 𝔽_q(Y) with F(s) equal to the generic point; reason: a rational map is a tuple of rational functions defined where its denominators do not vanish; same notion
--   - encoding: polynomial map 𝔸^T → SLₙ → matrix of polynomials with determinant 1; reason: a morphism to SLₙ is a polynomial matrix satisfying det = 1 identically
--   - encoding: Q_geom(H, m; ε) for integer m → `Qgeom` with real H, m and m = n² − 1 for SLₙ; reason: avoids natural subtraction; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
--   - encoding: Y = SLₙ (a variety of dimension n² − 1 ≥ 1, so n ≥ 2) → every n : ℕ; reason: for n ≤ 1, SLₙ(𝔽_q) is a single point and both laws are the point mass, so the extra instances are trivially true and no instance of the source changes
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Corollary 3.4, eqs. (13)–(14), p.12

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_Tshears
import Definitions.Def_TransvectionMixing_HasRationalSectionSL

namespace TransvectionMixing

/-- **Corollary 3.4** (conditional mixing from a rational section) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §3.3, p.12). Let
`Y = 𝔸^m` with `m ≥ 1`, or `Y = SLₙ`, and let `F : 𝔸^T → Y` be a polynomial map over `𝔽_q`
with a rational section over `𝔽_q` and coordinate degrees at most `H ≥ 2`. For
`0 < ε ≤ 1/4`, if `q ≥ Q_geom(H, dim Y; ε)` (eq. (14)), then `F` sends uniform coefficients to
a law within `ε/8` of the uniform law `π_Y` on `Y(𝔽_q)` in total variation.

**Formalization Note** A polynomial map `𝔸^T → SLₙ` is a matrix of polynomials with
determinant `1`; `dim SLₙ = n² − 1`. Rational sections are elements of the function field of
`Y` over `𝔽_q` (`HasRationalSectionAff`, `HasRationalSectionSL`). -/
theorem corollary_3_4_conditional_mixing_from_rational_section (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (T H : ℕ) (hH : 2 ≤ H) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    (∀ m : ℕ, 1 ≤ m → ∀ P : Fin m → MvPolynomial (Fin T) F,
        (∀ i, (P i).totalDegree ≤ H) → HasRationalSectionAff P →
        Qgeom H m ε ≤ Fintype.card F →
        MarkovMixing.tvDist (pushLawAff P) (unifOn (Fin m → F)) ≤ ε / 8) ∧
      (∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) (MvPolynomial (Fin T) F)),
        P.det = 1 → (∀ i j, (P i j).totalDegree ≤ H) → HasRationalSectionSL P →
        Qgeom H ((n : ℝ) ^ 2 - 1) ε ≤ Fintype.card F →
        MarkovMixing.tvDist (pushLawSL P) (unifOn (Matrix.SpecialLinearGroup (Fin n) F))
          ≤ ε / 8) := by sorry

end TransvectionMixing
