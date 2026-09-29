-- Prove2me | Theorems.Thm_PathCover_homotopic_concat_insert
-- name    : PathCover.homotopic_concat_insert
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T09:46:23.970707+00:00
-- url     : https://prove2.me/theorems/828ee417-68c4-4ad3-988c-f03ec689b9ba
-- title:
--   Inserting return paths: a chain of paths is homotopic to the concatenation of the loops it splices, whenever the two outer return paths are nullhomotopic
-- statement:
--   Let $X$ be a topological space and $x_0\in X$ a basepoint. Fix $n\ge 0$ and points $p_0,\dots,p_n$ of $X$. Suppose given
--
--   - for each $k<n$, a path $f_k$ from $p_k$ to $p_{k+1}$;
--   - for each $k\le n$, a path $g_k$ from $x_0$ to $p_k$;
--
--   and suppose $p_0 = x_0$ and $p_n = x_0$, and that $g_0$ and $g_n$, read as loops at $x_0$ by means of those two equalities, are **nullhomotopic**.
--
--   Then, reading the concatenation $f_0 f_1\cdots f_{n-1}$ as a loop at $x_0$ in the same way, it is homotopic rel endpoints to the concatenation of the $n$ loops
--
--   $$g_k \cdot f_k \cdot \overline{g_{k+1}},\qquad k = 0,\dots,n-1,$$
--
--   each of which is a loop at $x_0$. Here $\overline{g}$ denotes the reverse path.
--
--   Nothing at all is required of the intermediate paths $g_1,\dots,g_{n-1}$ beyond their endpoints: they need not come from any coherent system of choices, need not be related to the $f_k$, and need not be distinct. The conclusion holds for every choice of them, which is stronger than a reader might expect.
--
--   The point is that the inserted return paths cancel: consecutive terms meet in $\overline{g_{k+1}}\cdot g_{k+1}$, which is nullhomotopic, so the whole product telescopes back to $g_0\cdot(f_0\cdots f_{n-1})\cdot\overline{g_n}$ — and the two outer factors are nullhomotopic by hypothesis.
--
--   Two conventions are worth stating. The bracketing of both sides is fixed by `Path.concat`, which folds from the left starting at the constant path, so a family of $n$ paths yields $n+1$ pieces, the first of them constant; homotopy rel endpoints absorbs the difference between any two bracketings, and the leading constant piece appears on both sides. And the hypothesis on $g_0$ and $g_n$ is nullhomotopy rather than equality to the constant path — the weakest form the argument supports. A caller who happens to hold literal equality gets the hypothesis in one line.
--
--   The conclusion is homotopy of the actual paths, not merely equality of their classes in the fundamental groupoid.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, p. 35, proof of Lemma 1.15 (first paragraph for the subdivision, second for the inserted return paths). Stated here for a general open cover and a general path, independently of that context.

import Mathlib

open scoped unitInterval

namespace PathCover

theorem homotopic_concat_insert {X : Type*} [TopologicalSpace X] (x0 : X) {n : ℕ}
    (p : Fin (n + 1) → X)
    (f : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (g : (k : Fin (n + 1)) → Path x0 (p k))
    (h0 : p 0 = x0) (hn : p (Fin.last n) = x0)
    (hg0 : ((g 0).cast rfl h0.symm).Homotopic (Path.refl x0))
    (hgn : ((g (Fin.last n)).cast rfl hn.symm).Homotopic (Path.refl x0)) :
    ((Path.concat p f).cast h0.symm hn.symm).Homotopic
      (Path.concat (fun _ : Fin (n + 1) => x0)
        (fun k => (g k.castSucc).trans ((f k).trans (g k.succ).symm))) := by
  sorry

end PathCover
