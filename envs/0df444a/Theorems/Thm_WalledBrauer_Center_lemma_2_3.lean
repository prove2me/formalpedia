-- Prove2me | Theorems.Thm_WalledBrauer_Center_lemma_2_3
-- name    : WalledBrauer.Center.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:54.215601+00:00
-- url     : https://prove2.me/theorems/191c53d6-b075-46aa-b26f-cff86143c205
-- title:
--   Lemma 2.3 — relations between transpositions $(i,i')$ and arc elements $e_{i,j}$ in $B_{r,s}(\delta)$
-- statement:
--   In the walled Brauer algebra $B_{r,s}(\delta)$, write $(a,b)$ for the transposition of two vertices on the same side of the wall and $e_{i,j}$ ($1\le i\le r<j\le r+s$) for the diagram with top and bottom arcs joining $i$ and $j$. For mutually distinct indices for which every symbol below is defined (transpositions within one side, arcs across the wall), the following relations hold:
--
--   1. $(i',j')\,e_{i,j}=e_{i,j}\,(i',j')$;
--   2. $(i,i')\,e_{i,j}=e_{i',j}\,(i,i')$ and $(j,j')\,e_{i,j}=e_{i,j'}\,(j,j')$;
--   3. $e_{i,j}\,e_{i',j'}=e_{i',j'}\,e_{i,j}$;
--   4. $e_{i,j}\,e_{i,j'}=e_{i,j}\,(j,j')$ and $e_{i,j}\,e_{i',j}=e_{i,j}\,(i,i')$;
--   5. $e_{i,j}\,e_{i',j'}\,(i,i')=e_{i,j}\,e_{i',j'}\,(j,j')$.
--
--   These diagram identities are the computational input for the relations between Jucys–Murphy elements and generators (Proposition 2.4) and for Lemma 3.2.
--
--   **Formalization Note** Vertices are 0-based. Admissibility is spelled out per clause: in (1) $i<r\le j$ and $i',j'$ lie on one side of the wall; in (2)–(5) the arc ends satisfy $i,i'<r\le j,j'$. "Mutually distinct" is required of the indices occurring in each clause. The platform's product puts the left factor on top, the opposite of the paper's (p. 4). The relations are transcribed literally, in the page's order, with the platform's product; read in the paper's algebra each one is the image of the page's relation under the up–down flip, an anti-automorphism fixing every $(a,b)$ and $e_{i,j}$, so it holds equally.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, pp. 7–8, Lemma 2.3

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem lemma_2_3 (r s : ℕ) (δ : ℂ) :
    -- (1) `(i′, j′) e_{i,j} = e_{i,j} (i′, j′)`: `i < r ≤ j`, `i′, j′` on one side of the wall
    (∀ i j i' j' : Fin (r + s), i.val < r → r ≤ j.val →
        (i'.val < r ↔ j'.val < r) →
        i ≠ j → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' → i' ≠ j' →
        tr δ i' j' * eArc δ i j = eArc δ i j * tr δ i' j') ∧
    -- (2) `(i, i′) e_{i,j} = e_{i′,j} (i, i′)`: `i, i′ < r ≤ j`
    (∀ i i' j : Fin (r + s), i.val < r → i'.val < r → r ≤ j.val → i ≠ i' →
        tr δ i i' * eArc δ i j = eArc δ i' j * tr δ i i') ∧
    -- (2) `(j, j′) e_{i,j} = e_{i,j′} (j, j′)`: `i < r ≤ j, j′`
    (∀ i j j' : Fin (r + s), i.val < r → r ≤ j.val → r ≤ j'.val → j ≠ j' →
        tr δ j j' * eArc δ i j = eArc δ i j' * tr δ j j') ∧
    -- (3) `e_{i,j} e_{i′,j′} = e_{i′,j′} e_{i,j}`: `i, i′ < r ≤ j, j′`
    (∀ i j i' j' : Fin (r + s), i.val < r → i'.val < r → r ≤ j.val → r ≤ j'.val →
        i ≠ i' → j ≠ j' →
        eArc δ i j * eArc δ i' j' = eArc δ i' j' * eArc δ i j) ∧
    -- (4) `e_{i,j} e_{i,j′} = e_{i,j} (j, j′)`: `i < r ≤ j, j′`
    (∀ i j j' : Fin (r + s), i.val < r → r ≤ j.val → r ≤ j'.val → j ≠ j' →
        eArc δ i j * eArc δ i j' = eArc δ i j * tr δ j j') ∧
    -- (4) `e_{i,j} e_{i′,j} = e_{i,j} (i, i′)`: `i, i′ < r ≤ j`
    (∀ i i' j : Fin (r + s), i.val < r → i'.val < r → r ≤ j.val → i ≠ i' →
        eArc δ i j * eArc δ i' j = eArc δ i j * tr δ i i') ∧
    -- (5) `e_{i,j} e_{i′,j′} (i, i′) = e_{i,j} e_{i′,j′} (j, j′)`: `i, i′ < r ≤ j, j′`
    (∀ i j i' j' : Fin (r + s), i.val < r → i'.val < r → r ≤ j.val → r ≤ j'.val →
        i ≠ i' → j ≠ j' →
        eArc δ i j * eArc δ i' j' * tr δ i i' =
          eArc δ i j * eArc δ i' j' * tr δ j j') := by sorry
end WalledBrauer.Center
