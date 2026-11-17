-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_1_4
-- name    : RevRedSAT.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:58:47.009201+00:00
-- url     : https://prove2.me/theorems/dd11f0c1-3f5c-4e32-9eb5-ea3996676800
-- title:
--   Theorem 1.4 — q-Coloring and List q-Coloring in $2^{O_{q,h}(k\eta(k)/\sqrt{\lambda(k)})}n^{O_{q,h}(1)}$, $k$ the minimum treedepth-$h$ modulator
-- statement:
--   Fix integers $q\ge2$ and $h\ge1$, and let $\lambda(t)=\log_2(t+2)$, $\eta(t)=\log_2\log_2(t+4)$. For a graph $G$ with $n$ vertices let
--
--   $$k=\min\{|X| : \mathrm{td}(G-X)\le h\}$$
--
--   be the minimum size of a treedepth-$h$ modulator.
--
--   Assume the Quantitative $d$-SAT Assumption 4.2. Then there are deterministic algorithms and constants $C,c$ (depending on $q$ and $h$) that decide $q$-Coloring and List $q$-Coloring within
--
--   $$\Bigl\lfloor 2^{C\,k\eta(k)/\sqrt{\lambda(k)}}\,(n+2)^{c}\Bigr\rfloor$$
--
--   steps. The modulator is not part of the input.
--
--   Over a modulator of bounded treedepth, the colors of the deleted vertices are the only variables of the SAT encoding, so the exponent depends on $k$ and not on $n$.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: 2^{O_{q,h}(k log log k/√log k)} → 2^{C·kη(k)/√λ(k)} with λ(t) = log₂(t+2), η(t) = log₂log₂(t+4); reason: the two exponents differ by a factor tending to 1 and both are covered by the constant C; the paper's own form (§3, Corollary 7.5, p.54) is defined at k = 0, 1
--   - reading: n^{O_{q,h}(1)} → (n + 2)^c; reason: the graph with no vertices is handled in constant time (§3, p.27); for n ≥ 1, (n+2)^c ≤ (3n)^c
--   - reading: q-Coloring and List q-Coloring admit deterministic algorithms → decision algorithms (DecideWithin); reason: App. C.2 defines q-Coloring as asking whether such a map exists
--   - encoding: colors [q] = {1, …, q} → colors Fin q; reason: relabelling
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 1.4, p.6 (printed) = PDF p.8; App. C.2, p.93; Corollary 7.5, p.54

import Mathlib
import Definitions.Def_RevRedSAT_QuantDSAT
import Definitions.Def_RevRedSAT_Supplement_DecideWithin
import Definitions.Def_RevRedSAT_Supplement_ColInstance

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 1.4 (q-Coloring and List q-Coloring by a treedepth-h modulator).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 1.4, p.6: "Fix integers q ≥ 2 and h ≥ 1. Under the Quantitative d-SAT Assumption,
q-Coloring and List q-Coloring admit deterministic algorithms running in time
2^{O_{q,h}(k log log k/√log k)}n^{O_{q,h}(1)}, where n = |V(G)| and k is the minimum size of a set X
such that G − X has treedepth at most h. The set X need not be supplied."

Under Assumption 4.2, for all `q ≥ 2` and `h ≥ 1` there are machines with finite alphabets and
constants `C, c` (depending on `q, h`) deciding q-Coloring and List q-Coloring on every code of
every instance within `⌊2^{C·kη(k)/√λ(k)} · (n + 2)^c⌋` steps, `k` the minimum treedepth-`h`
modulator size of the graph (`modNum`), which is not part of the input.

**Formalization Note** The rate is written with `λ(t) = log₂(t + 2)`, `η(t) = log₂ log₂(t + 4)`
(`RevRedSAT.vcRate`), as in Corollary 7.5 (p.54), the formal form of this theorem; it differs from
the printed `log log k/√log k` by a factor tending to `1` and is defined at `k = 0, 1`.
`n^{O(1)}` is `(n + 2)^c`, so the graph with no vertices gets a constant bound (§3, p.27). Decision
only (App. C.2, "asks whether such a map exists"). -/
theorem theorem_1_4 :
    QuantDSAT → ∀ q h : ℕ, 2 ≤ q → 1 ≤ h →
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        DecideWithin M IsColCode (Colorable q)
          (fun I _ => expBound (vcRate C (modNum h I.G)) (I.n + 2) c)) ∧
      (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ (C : ℝ) (c : ℕ),
        DecideWithin M (IsListColCode (q := q)) ListColorable
          (fun I _ => expBound (vcRate C (modNum h I.G)) (I.n + 2) c)) := by sorry

end RevRedSAT.Supplement
