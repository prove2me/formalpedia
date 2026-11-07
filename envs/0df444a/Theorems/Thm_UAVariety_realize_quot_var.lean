-- Prove2me | Theorems.Thm_UAVariety_realize_quot_var
-- name    : UAVariety.realize_quot_var
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T17:30:18.983168+00:00
-- url     : https://prove2.me/theorems/d32d75bf-d19e-41f3-8f94-a137bd10d235
-- title:
--   A term evaluated at the generators of T(X)/φ is its own class
-- statement:
--   $L$ is a signature without relation symbols (`[L.IsAlgebraic]`); an algebra is an $L$-structure (`Alg L` bundles one). The term algebra $T(X)$ is `L.Term X` with the operations building terms; `t.realize v` is the value of the term $t$ in an algebra under the assignment $v$ of the variables. $A\models p\approx q$ (`Satisfies A (p, q)`) means $p^A(v)=q^A(v)$ for every assignment $v:X\to A$. A congruence (`Congruence M`) is an equivalence relation on $M$ compatible with the operations, and `φ.Quot` is the quotient algebra $M/\varphi$ (Mathlib's quotient structure, `Quotient.mk φ.toSetoid a` $= a/\varphi$).
--
--   **Claim.** Let $\varphi$ be a congruence on the term algebra $T(X)$. For every term $p\in T(X)$, $p^{T(X)/\varphi}(\bar x)=p/\varphi$, where $\bar x$ is the assignment $x\mapsto x/\varphi$.
-- source:
--   S. Burris, H. P. Sankappanavar, A Course in Universal Algebra, Millennium Edition (2012), https://www.math.uwaterloo.ca/~snburris/htdocs/ualg.html, Ch. II, §10–11 (proof of Thm 11.4, using Def 10.4 and Lemma 10.8)

import Definitions.Def_UAVariety_defs

universe u v w

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u, v}} [L.IsAlgebraic]

/-- Generic elements of a quotient of the term algebra: evaluating a term `p` in `T(X)/φ` at the classes of the variables gives the class of `p` (used in B&S Thm 11.4). -/
theorem realize_quot_var {X : Type*} (φ : Congruence (L := L) (L.Term X)) (p : L.Term X) :
    p.realize (fun x => (Quotient.mk φ.toSetoid (Term.var x) : φ.Quot)) =
      Quotient.mk φ.toSetoid p := by sorry

end UAVariety
