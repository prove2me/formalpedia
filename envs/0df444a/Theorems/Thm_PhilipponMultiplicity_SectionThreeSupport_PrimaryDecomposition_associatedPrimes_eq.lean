-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_PrimaryDecomposition_associatedPrimes_eq
-- name    : PhilipponMultiplicity.SectionThreeSupport.PrimaryDecomposition.associatedPrimes_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:15.783554+00:00
-- url     : https://prove2.me/theorems/6eb8bedc-9421-481a-aac4-ac866b98b943
-- title:
--   Associated primes of the actual minimal primary decomposition
-- statement:
--   For a genuine finite minimal homogeneous primary decomposition $I=\bigcap_i Q_i$, $$\operatorname{Ass}(R/I)=\{\sqrt{Q_i}:i\}.$$ This identifies the quotient module’s actual associated primes, including embedded ones; it does not assume the identification as part of the decomposition data.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, primary-decomposition foundations used in Facts B–E, printed pp. 365–369, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.PrimaryDecomposition.associatedPrimes_eq
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
      Set.range (fun i => (D.component i).radical) := by sorry
