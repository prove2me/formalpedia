-- Prove2me | Theorems.Thm_SpectralFeedback_horn_cone_convexity
-- name    : SpectralFeedback.horn_cone_convexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:38.73584+00:00
-- url     : https://prove2.me/theorems/e3265b31-d56e-4ea7-ba1d-f0617c60aab3
-- title:
--   Horn-cone convexity [KT99] — feasible spectral triples form a convex cone, symmetric in the summands
-- statement:
--   For every $n$, let $\mathcal H_n$ be the set of spectral triples $(\lambda^\downarrow(A),\lambda^\downarrow(B),\lambda^\downarrow(A+B))$ of complex Hermitian $n\times n$ matrices $A,B$. Then:
--
--   1. $\mathcal H_n$ is a cone: $t\,p\in\mathcal H_n$ for $p\in\mathcal H_n$ and $t\ge0$;
--   2. $\mathcal H_n$ is convex;
--   3. $\mathcal H_n$ is invariant under exchanging the two summands: $(a,b,c)\in\mathcal H_n\Rightarrow(b,a,c)\in\mathcal H_n$;
--   4. every feasible triple is realized at any prescribed sum: if $(a,b,c)\in\mathcal H_n$ and $C$ is Hermitian with $\lambda^\downarrow(C)=c$, then there are Hermitian $A,B$ with
--   $$
--   A+B=C,\qquad\lambda^\downarrow(A)=a,\qquad\lambda^\downarrow(B)=b .
--   $$
--
--   This is the classical theorem of Klyachko and Knutson–Tao that the paper cites. In the proof of Theorem H.2 it averages the feasible triples $(a,b,\lambda)$ and $(b,a,\lambda)$ of an optimal pair, producing two atoms with the common spectrum $x=(a+b)/2$ and the same sum $R$ after a common conjugation.
--
--   **Formalization Note** Spectra are 0-based decreasing vectors (`eigDesc`). The statement is the cited theorem in full generality, for every $n$ and all complex Hermitian matrices, not only the balanced case used in the proof.
--
--   Differences from the source:
--   - encoding: the real Horn cone of feasible spectral triples $(a,b,\lambda)$ → `hornSet n`: triples `(eigDesc A, eigDesc B, eigDesc (A+B))` of complex Hermitian `A, B`, as `Fin n → ℝ` vectors; reason: Lean indexing convention; same set
--   - encoding: the same sum after a common conjugation → for every Hermitian `C` with `eigDesc C = c` there are Hermitian `A, B` with `A + B = C` and spectra `a, b`; reason: the realization at a prescribed sum is what "after a common conjugation" means; same content
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), proof of Theorem H.2, p.109 (PDF p.111); proof of Theorem F.4, p.94 (PDF p.96); citing [KT99] A. Knutson and T. Tao, The honeycomb model of GL_n(C) tensor products I, J. Amer. Math. Soc. 12 (1999)

import Mathlib
import Definitions.Def_SpectralFeedback_hornSet

namespace SpectralFeedback

/-- **Horn-cone convexity** [KT99] (Qi, *Spectral Structure and Exact Arithmetic of Finite-Feedback
Measurement Discrimination*, manuscript (Nov. 2026), proof of Theorem H.2, p.109 (PDF p.111): "The
real Horn cone is convex and invariant under exchanging the two summands. Consequently the average
of the feasible triples `(a, b, λ)` and `(b, a, λ)` is feasible. It supplies two atoms with the
common spectrum `x = (a + b)/2`, … and the same sum after a common conjugation"; proof of
Theorem F.4, p.94: "a convex cone invariant under exchanging `a, b`").

For every `n`, the set of spectral triples `(λ↓(A), λ↓(B), λ↓(A + B))` of complex Hermitian
`n × n` matrices is (1) a cone, (2) convex, (3) invariant under exchanging the two summands, and
(4) every triple `(a, b, c)` in it is realized at any prescribed Hermitian `C` with spectrum `c`:
there are Hermitian `A, B` with `A + B = C`, `λ↓(A) = a`, `λ↓(B) = b`.

**Formalization Note** Spectra are decreasing, 0-based `Fin n → ℝ` (`eigDesc`). This is the cited
theorem of Klyachko and Knutson–Tao in full generality (all `n`, all Hermitian matrices), not only
the balanced special case used in the proof. -/
theorem horn_cone_convexity (n : ℕ) :
    (∀ t : ℝ, 0 ≤ t → ∀ p ∈ hornSet n, t • p ∈ hornSet n) ∧
    Convex ℝ (hornSet n) ∧
    (∀ a b c : Fin n → ℝ, (a, b, c) ∈ hornSet n → (b, a, c) ∈ hornSet n) ∧
    (∀ a b c : Fin n → ℝ, (a, b, c) ∈ hornSet n →
      ∀ C : Matrix (Fin n) (Fin n) ℂ, C.IsHermitian →
        (fun i : Fin n => eigDesc C (i : ℕ)) = c →
        ∃ A B : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian ∧ B.IsHermitian ∧ A + B = C ∧
          (fun i : Fin n => eigDesc A (i : ℕ)) = a ∧
          (fun i : Fin n => eigDesc B (i : ℕ)) = b) := by sorry

end SpectralFeedback
