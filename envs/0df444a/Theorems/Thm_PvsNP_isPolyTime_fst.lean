-- Prove2me | Theorems.Thm_PvsNP_isPolyTime_fst
-- name    : PvsNP.isPolyTime_fst
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T06:30:20.085418+00:00
-- url     : https://prove2.me/theorems/57acd134-8986-4015-89d7-8c98dbd9fb34
-- title:
--   The first projection of a pair is polynomial-time computable
-- statement:
--   Let $\alpha$ and $\beta$ be types with canonical bitstring encodings, and encode a pair as the self-delimiting block of the encoding of its first component followed by the encoding of its second component,
--
--   $$\mathrm{enc}(a,b) \;=\; \mathrm{delimit}\bigl(\mathrm{enc}(a)\bigr) \,\Vert\, \mathrm{enc}(b),$$
--
--   where $\mathrm{delimit}$ replaces each payload bit $c$ by the two bits $1c$ and terminates the block with $0$. Then the first projection $(a,b) \mapsto a$ is computable in polynomial time by a two-stack Turing machine with respect to these encodings.
--
--   Concretely, the machine has to output $\mathrm{enc}(a)$ given $\mathrm{delimit}(\mathrm{enc}(a)) \Vert \mathrm{enc}(b)$: it reads the input from the left, and as long as it sees the flag bit $1$ it copies the following payload bit, stopping at the terminator $0$ and discarding the remainder of the input. This is a purely syntactic scan that does not depend on the encodings of $\alpha$ and $\beta$, and it runs in time linear in the length of the input (the stack discipline of the machine model may require one auxiliary reversal, which is again linear).
--
--   The statement is the projection half of the elementary toolkit for polynomial-time computability: combined with closure under composition, it shows that a polynomial-time decision procedure for a problem yields a polynomial-time verifier that ignores its witness.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 1, Section 1.2 (representing pairs of strings and elementary string manipulations in linear time) and Chapter 2, Definition 2.1 (verifier ignoring its certificate); pair encoding as in the platform definition PvsNP_bitstring_encoding, adapted from google-deepmind/formal-conjectures, FormalConjecturesForMathlib/Computability/BitstringEncoding.lean.

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem isPolyTime_fst {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.fst : α × β → α) := by sorry

end PvsNP
