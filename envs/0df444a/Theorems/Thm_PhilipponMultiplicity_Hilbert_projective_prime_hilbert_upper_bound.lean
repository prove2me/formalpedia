-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_projective_prime_hilbert_upper_bound
-- name    : PhilipponMultiplicity.Hilbert.projective_prime_hilbert_upper_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-10T20:09:32.445227+00:00
-- url     : https://prove2.me/theorems/2186aeef-5c87-4ae3-bfe6-164947233ac4
-- title:
--   Chardin's upper Hilbert bound for a projective prime ideal
-- statement:
--   Let $K$ be an algebraically closed field, and let $\mathfrak p$ be a relevant homogeneous prime ideal in the coordinate ring of $\mathbf P^N_K$. Write $r$ for the degree of its actual Hilbert polynomial and $\delta$ for $r!$ times its leading coefficient. Then, for every integer $m\ge0$,
--   $$
--   \dim_K(K[X_0,\ldots,X_N]/\mathfrak p)_m\le\delta\binom{m+r}{r}.
--   $$
--   Relevance excludes the irrelevant maximal ideal, whose Hilbert polynomial is zero. This is Chardin's classical upper bound in the prime, algebraically closed case. The intended application uses $m=2$ after a positive-multidegree Segre–Veronese embedding. All dimensions and degrees in the formal statement are extracted from the existing quotient Hilbert function; no estimate is supplied as structure data.
--
--   This theorem is an Open proof obligation, not an assumed change to either corrected addendum.
-- source:
--   M. Chardin, Une majoration de la fonction de Hilbert et ses conséquences pour l'interpolation algébrique, central theorem (PDF p. 2), prime-case proof §I(b) (PDF pp. 3–5), https://webusers.imj-prg.fr/~marc.chardin/publications/textes/01.Hilbert.pdf . The formal statement specializes to algebraically closed fields and relevant homogeneous primes.

import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false

namespace PhilipponMultiplicity.Hilbert
open SectionThree

/-- Chardin's ordinary projective Hilbert upper bound. Relevance excludes
the irrelevant maximal ideal, whose Hilbert polynomial is zero. -/
theorem projective_prime_hilbert_upper_bound
    (K : Type*) [Field K] [IsAlgClosed K]
    (N : ℕ) (p : Ideal (projectiveSpace K N).CoordinateRing)
    (hp : p.IsPrime) (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) p)
    (hrel : IsRelevant K 1 (fun _ => N) p) (m : ℕ) :
    (hilbertFunction K 1 (fun _ => N) p (fun _ => m) : ℚ) ≤
      (Nat.choose (m + idealDimension (projectiveSpace K N) p)
        (idealDimension (projectiveSpace K N) p) : ℚ) *
        idealDegreeValue (projectiveSpace K N) p (fun _ => 1) := by sorry

end PhilipponMultiplicity.Hilbert
