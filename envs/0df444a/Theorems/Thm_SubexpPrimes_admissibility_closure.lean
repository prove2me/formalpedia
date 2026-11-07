-- Prove2me | Theorems.Thm_SubexpPrimes_admissibility_closure
-- name    : SubexpPrimes.admissibility_closure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:46.096251+00:00
-- url     : https://prove2.me/theorems/a914195d-bec5-4318-99eb-e74078561603
-- title:
--   §2.2 — prescribed bits, intervals and circuits are admissible, and admissibility is closed under conjunction and prefixes
-- statement:
--   The following families of constraints on $n$-bit strings are admissible:
--
--   1. prescribed bits at given positions;
--   2. interval bounds $\mathrm{lo}\le x\le\mathrm{hi}$;
--   3. for any constant $K$, circuits with at most $Kn$ gates.
--
--   The conjunction of two admissible families is admissible, and a prefix condition $x$ begins with $\pi$ can be added to any admissible family, with $\pi$ as part of the description.
--
--   This is what the search by prefixes requires: Theorem 1 uses the always-true constraint, the condition that the top bit is $1$, and all prefixes.
--
--   Differences from the source:
--   - reading: there is a network → an explicit family: one builder machine, one entry machine, one constant, all polynomial; reason: Definition 2.3 and p.28 ("the arithmetic parts are explicit, and the rotation constants take time poly(p)") claim it, and Theorem 2.5 evaluates only such networks; this is the stronger reading and it implies the bare existence
--   - reading: the conjunction of a constant number of admissible constraints → the conjunction of two families, iterated; reason: a constant number is a constant number of binary steps
--   - reading: circuits with O(n) gates → for each K, the family that accepts when the circuit has at most Kn gates and outputs 1; reason: admissibility has one set of constants, so the bound on the size must be fixed before the family
--   - encoding: admissible: constructed, and entries computed, in time poly(n + L) → builder and entry machine bounded in time and space by one polynomial; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), §2.2 after Definition 2.3, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_bitsToNat
import Definitions.Def_SubexpPrimes_Circuit

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Admissibility closure** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), §2.2, p.15.

"Prescribed bits, interval bounds, and circuits with `O(n)` gates are admissible. The conjunction of
a constant number of admissible constraints is admissible … In particular, a prefix condition can be
added to any admissible constraint." The conjunction is stated for two families, with the paired
description; a prefix `π` is part of the description, and a prefix longer than `n` is never satisfied.

**Formalization Note.** Prescribed bits are a list of (position, bit), counted from the most
significant bit. An interval is `lo ≤ x ≤ hi`, with `lo`, `hi` in binary. A circuit "with `O(n)`
gates" is the family, for one constant `K`, that accepts when the circuit has at most `K n` gates and
outputs `true`; a larger circuit is rejected outright, so it does not enter the size bound. -/
theorem admissibility_closure :
    (∀ (δ₁ δ₂ : Type) (enc₁ : δ₁ → List Bool) (enc₂ : δ₂ → List Bool)
        (C₁ : ℕ → δ₁ → List Bool → Prop) (C₂ : ℕ → δ₂ → List Bool → Prop),
      Admissible enc₁ C₁ → Admissible enc₂ C₂ →
      Admissible (fun d : δ₁ × δ₂ => Encoding.encodeList id [enc₁ d.1, enc₂ d.2])
        (fun n d x => C₁ n d.1 x ∧ C₂ n d.2 x)) ∧
    (∀ (δ : Type) (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop),
      Admissible encD C →
      Admissible (fun d : δ × List Bool => Encoding.encodeList id [encD d.1, d.2])
        (fun n d x => C n d.1 x ∧ d.2 <+: x)) ∧
    (Admissible (fun ps : List (ℕ × Bool) =>
        Encoding.encodeList (fun p => Encoding.encodeNat p.1 ++ [p.2]) ps)
      (fun _ ps x => ∀ p ∈ ps, x[p.1]? = some p.2)) ∧
    (Admissible (fun d : ℕ × ℕ => Encoding.encodeList countWord [d.1, d.2])
      (fun _ d x => d.1 ≤ bitsToNat x ∧ bitsToNat x ≤ d.2)) ∧
    (∀ K : ℕ, Admissible Circuit.encode
      (fun n c x => c.length ≤ K * n ∧ c.eval x = true)) := by sorry

end SubexpPrimes
