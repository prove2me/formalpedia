-- Prove2me | Theorems.Thm_TuranMatching_Clique_turan_increment
-- name    : TuranMatching.Clique.turan_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:20.042445+00:00
-- url     : https://prove2.me/theorems/c6389f10-87a3-4856-8621-9ccd17cda6a2
-- title:
--   §2, p. 4, Case 4 — $t(N+1,k)-t(N,k)=N-\lfloor N/k\rfloor$ is non-decreasing in $N$ with steps at most $1$
-- statement:
--   Let $k\ge1$ and $N\ge0$, and write $\Delta(N)=t(N+1,k)-t(N,k)$. Then
--
--   1. $\Delta(N)=N-\lfloor N/k\rfloor$, the total size of the largest $k-1$ classes of $T(N,k)$;
--   2. $\Delta(N)\le\Delta(N+1)$;
--   3. $\Delta(N+1)\le\Delta(N)+1$.
--
--   Equivalently, when the number of vertices decreases by one, $\Delta$ can only decrease, and by at most $1$:
--   $$0\ \le\ \Delta(N+1)-\Delta(N)\ \le\ 1 .$$
--
--   This is the fact behind the discrete convexity of $f$ in Case 4.
--
--   **Formalization Note** The differences are computed in ℤ; $\lfloor N/k\rfloor$ is natural division. The statement holds for every $k\ge1$; the paper uses it for $k\ge2$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 4, Case 4 ("When b increases by 1, … by at most 1 …")

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem turan_increment (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ((turanNum (N + 1) k : ℤ) - turanNum N k = (N : ℤ) - (N / k : ℕ)) ∧
    ((turanNum (N + 1) k : ℤ) - turanNum N k ≤ (turanNum (N + 2) k : ℤ) - turanNum (N + 1) k) ∧
    ((turanNum (N + 2) k : ℤ) - turanNum (N + 1) k ≤ (turanNum (N + 1) k : ℤ) - turanNum N k + 1) := by sorry

end TuranMatching.Clique
