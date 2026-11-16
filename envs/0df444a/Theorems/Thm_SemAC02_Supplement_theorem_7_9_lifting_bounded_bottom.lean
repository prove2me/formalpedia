-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_7_9_lifting_bounded_bottom
-- name    : SemAC02.Supplement.theorem_7_9_lifting_bounded_bottom
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:53:55.896698+00:00
-- url     : https://prove2.me/theorems/aec339f7-3552-4719-885b-24f87354a00c
-- title:
--   Theorem 7.9 — lifting to bounded bottom degree
-- statement:
--   Let $F$ be a CNF on $y_1,\dots,y_n$, $q\ge2$, $\mathbb F$ any field, and let $\pi$ be an arity-2 semantic ΣΠΣΠ-PC refutation of $\mathrm{Lift}_q(F)$ over $\mathbb F$. For every integer $d\ge1$ with $M_{\mathrm{bot}}(\pi)<q^{d+1}$ there is an arity-2 semantic ΣΠΣΠ[$d$]-PC refutation $\pi'$ of $F$ with
--
--   $$
--   S(\pi')\le S(\pi), \tag{38}
--   $$
--
--   and $\pi'$ has no more proof lines and no more top product-term occurrences than $\pi$. In particular, the theorem applies with
--
--   $$
--   d=\max\{1,\lfloor\log_qM_{\mathrm{bot}}(\pi)\rfloor\}.
--   $$
--
--   It transfers bounded-bottom-fan-in lower bounds to unrestricted semantic ΣΠΣΠ-PC (Corollaries 7.10, 7.11 and Theorem 7.12).
--
--   **Formalization Note** The proof vertices are the lines. ΣΠΣΠ[$d$] is taken with bottom product gates of fan-in at most $d$.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - generalization: ΣΠΣΠ[d]-PC: bottom polynomials of degree ≤ d after multilinearisation (p.54) → IsSPSP d: every bottom product gate has fan-in ≤ d; reason: fan-in ≤ d implies multilinear degree ≤ d, so π' is a ΣΠΣΠ[d]-PC refutation in the sense of p.54
--   - reading: the number of proof vertices → π'.length ≤ π.length; reason: V(π) is the set of proof lines ((32), p.55)
--   - encoding: a CNF F → a list of clauses; reason: the axiom set and satisfiability do not depend on order or repetition
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 7.9, p.56 (PDF p.58); §7.3.1–7.3.2, pp.54–55 (PDF pp.56–57)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Supplement_selLift

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 7.9 (Lifting to bounded bottom degree)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 7.9, p.56): let `π` be a semantic ΣΠΣΠ-PC refutation of `Lift_q(F)` over a field `𝔽`. For
every integer `d ≥ 1` such that `M_bot(π) < q^{d+1}`, there is a semantic ΣΠΣΠ[d]-PC refutation
`π'` of `F` with `S(π') ≤ S(π)` (38). The projection also does not increase the number of proof
vertices or product-term occurrences. In particular, the theorem applies with
`d = max{1, ⌊log_q M_bot(π)⌋}`.

**Formalization Note** `F` is a CNF on `y₁, …, y_n` given as a list of clauses and `q ≥ 2`
(§7.3.2, p.55); the axioms are the clause polynomials over `𝔽`. The proof vertices are the lines
(`π.length`), the product-term occurrences are `topOcc`. ΣΠΣΠ[d] is taken in the bottom fan-in
sense of §2 (every bottom product gate has fan-in at most `d`), which implies the degree bound of
§7.3.1. `⌊log_q M⌋` is `Nat.log q M`; the last conjunct says that this `d` satisfies the
hypothesis. -/
theorem theorem_7_9_lifting_bounded_bottom {𝔽 : Type} [Field 𝔽] {n q : ℕ} (hq : 2 ≤ q)
    (F : List (LiftSAParity.Clause (Fin n))) (π : List (ACirc 𝔽 (Fin n × Bool × Fin q)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ
      (clauseAx {C | C ∈ selLift q F}) π) :
    (∀ d : ℕ, 1 ≤ d → Mbot π < q ^ (d + 1) →
      ∃ π' : List (ACirc 𝔽 (Fin n)),
        IsSemPCRef (IsSPSP (d : ℕ∞)) Set.univ (clauseAx {C | C ∈ F}) π' ∧
        topS Set.univ π' ≤ topS Set.univ π ∧
        π'.length ≤ π.length ∧ topOcc π' ≤ topOcc π) ∧
    Mbot π < q ^ (max 1 (Nat.log q (Mbot π)) + 1) := by sorry

end SemAC02.Supplement
