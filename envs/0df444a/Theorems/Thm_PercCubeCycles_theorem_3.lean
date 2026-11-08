-- Prove2me | Theorems.Thm_PercCubeCycles_theorem_3
-- name    : PercCubeCycles.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:30.326202+00:00
-- url     : https://prove2.me/theorems/a3d5b34d-ed8c-4450-8b4d-cfd26227f46a
-- title:
--   Theorem 3 — locally expanding graphs have disjoint cycles of length $\ge\lceil ck/10\rceil$ covering $\frac17\frac cC|V|$ vertices, in $O(|E|^2)$ time
-- statement:
--   Let $k\ge1$ be an integer, $0<c\le C$, and $I=[I_{\min},I_{\max}]$ with $I_{\min}=\min\{ck/10,\,ck/(10C)\}$, $I_{\max}=\max\{10Ck/c,\,10Ck\}$. Let $G$ be a connected graph on more than $k$ vertices such that every almost connected set $W\subseteq V(G)$ with $|W|\in I$ satisfies
--
--   1. (P1) $c|W|\le|N(W)|\le C|W|$, and
--   2. (P2) for every $Z\subseteq N(W)$, $e(W,Z)\le|Z|+c^2k/10$.
--
--   Let $\ell=ck/10$. If $2<\ell$, then $G$ contains a family of pairwise vertex disjoint cycles of length at least $\lceil\ell\rceil$, covering at least
--   $$\frac17\frac cC|V(G)|$$
--   vertices. Such a family can be found in $O(|E(G)|^2)$ time.
--
--   This is the packing step of the main proof, and it is of independent interest.
--
--   Differences from the source:
--   - reading: $I_{\min}=\min\{ck/10,ck/10C\}$ → $\min\{ck/10,\,ck/(10C)\}$; reason: the counterpart of $10Ck/c$; the parse $(ck/10)C$ gives $I_{\min}<m$ in the application on p.10, so the proof of Theorem 1 would not apply
--   - reading: time bound with no machine named → one program and one constant $K$ for all instances, at most $K|E(G)|^2$ steps on every coin sequence and for every admissible word width; reason: the paper names no machine; this is the published word RAM with every instruction charged one step
--   - encoding: a procedure with real parameters $c,C$ → the program receives $n$, the edge list, $k$, $\lceil ck/10\rceil$, $\lceil h/2\rceil$, $\lfloor h\rfloor$ with $h=\max\{k,ck\}$; reason: the procedure on p.11 compares sizes only with these integers, and a real number has no word encoding; the program is not restricted to rational $c,C$
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 3, p.4

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_PercCubeCycles_Packing

set_option autoImplicit false

open MatroidSensOracle

namespace PercCubeCycles

/-- Theorem 3, p.4, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `k ≥ 1`, `0 < c ≤ C`, `I = [I_min, I_max]`, and let `G` be a connected graph
on more than `k` vertices such that every almost connected `W` with `|W| ∈ I` satisfies (P1)
`c|W| ≤ |N(W)| ≤ C|W|` and (P2) `e(W, Z) ≤ |Z| + c²k/10` for every `Z ⊆ N(W)`. With `ℓ = ck/10`, if `2 < ℓ`
then `G` contains a family of pairwise vertex disjoint cycles of length at least `⌈ℓ⌉` covering at
least `(1/7)(c/C)|V(G)|` vertices. Such a family can be found in `O(|E(G)|²)` time.

**Formalization Note.** The time clause is read on the word RAM: one program and one `K` for all
instances, on every coin sequence and every admissible word width. The output is the number of
cycles, then for each cycle its length and vertices. -/
theorem theorem_3 :
    (∀ (V : Type) [Fintype V] (k : ℕ) (c C : ℝ) (G : SimpleGraph V), 1 ≤ k → 0 < c → c ≤ C →
      PackingHyp k c C G → 2 < c * k / 10 → ∃ F, IsCyclePacking k c C G F) ∧
    ∃ (P : List Instr) (K b : ℕ),
      ∀ (n k : ℕ) (c C : ℝ) (G : SimpleGraph (Fin n)), 1 ≤ k → 0 < c → c ≤ C →
        PackingHyp k c C G → 2 < c * k / 10 →
        ∀ (ω : Coins) (w : ℕ), WidthOK b (packingInput k c G) w →
          ∃ mem, exec P ω (K * G.edgeSet.ncard ^ 2) 0 0 (loadWords w (packingInput k c G)) = some mem ∧
            ∃ F : List (List (Fin n)), IsCyclePacking k c C G F ∧
              OutputsWords mem (F.length :: F.flatMap fun l => l.length :: l.map Fin.val) := by sorry

end PercCubeCycles
