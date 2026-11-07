-- Prove2me | Theorems.Thm_PDSEquiv_theorem_8_1
-- name    : PDSEquiv.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:19.330413+00:00
-- url     : https://prove2.me/theorems/11a9bdcf-dfd2-49e9-99b9-530f12a5f24e
-- title:
--   Theorem 8.1 — the eight planted dense subgraph conjectures (weak/strong search/decision, fixed-$k$ and binomial-$k$) are equivalent
-- statement:
--   Fix rationals $0<q<p\le1$ and any infinite set $\mathcal N\subseteq\mathbb N$, and let $\Lambda_N(k)$ be as in (4). The following eight claims are equivalent; in each, "there exist a randomized polynomial-time algorithm, a rational $\beta\in(0,1/2)$ and a constant $>0$ such that for all sufficiently large $N\in\mathcal N$":
--
--   1. (WS) $\Pr_{S,(G,C)\sim\mathrm{PDS}(N,\lfloor N^\beta\rfloor,p,q)}[S(G)=C]\ge N^{-a_0}$;
--   2. (SS) the same probability $\ge1-e^{-N^\xi}$;
--   3. (WD) $\mathrm{adv}_D(\mathrm{PDS}(N,\lfloor N^\beta\rfloor,p,q),\mathrm{ER}(N,q))\ge(1+\varepsilon)\Lambda_N(\lfloor N^\beta\rfloor)$;
--   4. (SD) the same advantage $\ge2-e^{-N^\xi}$;
--   5. (W̃S) $\Pr_{S,(G,C)\sim\widetilde{\mathrm{PDS}}(N,N^\beta,p,q)}[S(G)=C]\ge N^{-a_0}$;
--   6. (S̃S) the same probability $\ge1-e^{-N^\xi}$;
--   7. (W̃D) $\mathrm{adv}_D(\widetilde{\mathrm{PDS}}(N,N^\beta,p,q),\mathrm{ER}(N,q))\ge(1+\varepsilon)\Lambda_N(\lfloor N^\beta\rfloor)$;
--   8. (S̃D) the same advantage $\ge2-e^{-N^\xi}$.
--
--   The exponent $\beta$ and the other constants may differ between assertions. The reductions preserve $(p,q)$, the number $N$ of vertices and the set $\mathcal N$; they run in polynomial time, make $\mathrm{poly}(N)$ oracle queries on $N$-vertex graphs, and do not check membership in $\mathcal N$.
--
--   Here $\mathrm{adv}$ is in the normalization of §4.2 (values up to $2$), $\mathrm{PDS}$ plants a uniformly random $\lfloor N^\beta\rfloor$-set and $\widetilde{\mathrm{PDS}}$ a $\mathrm{Bin}([N],N^\beta/N)$-set. The theorem says that, for planted sets of size $N^{\beta}$ with $\beta<1/2$, beating edge counting by any constant factor is exactly as hard as recovering the planted set, in either model.
--
--   Differences from the source:
--   - encoding: the claims are equivalent (for every infinite 𝒩) → List.TFAE of the assertions, each an ∃ program, rational β ∈ (0, 1/2), constant, N₀ with the guarantee for all N ∈ 𝒩 with N ≥ N₀; reason: the printed assertions
--   - reading: the closing sentence: the reductions preserve (p, q), N and 𝒩, run in polynomial time, make poly(N) oracle queries on N-vertex graphs, and do not check membership in 𝒩 → a conjunct ∀ X Y in the list, Reduces p q X Y: for every β and constant of X, one oracle program, β′, a constant of Y, an exponent c and a threshold N₀ chosen before the oracle; for every oracle of X's kind, (N+2)^c time and queries on N-vertex graphs for every N and graph, and for every N ≥ N₀ the guarantee of X at size N implies that of Y at size N; reason: the sentence sits inside the theorem environment and is a claim; pointwise-in-N with no 𝒩 in it is what preserving 𝒩 without checking membership means, and it is what each arrow of the proof gives
--   - encoding: adv_D in the normalization of §4.2 → 2·|Pr_{D₁}[accept] − Pr_{D₂}[accept]|, acceptance being the output [1]; reason: the page's normalization, adv ≤ 2
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: an algorithm receives the graph and reads N from it; S(G) = C; D(G) ∈ {−1, 1} → input cells enc G = N :: the edge indicators of G in lexicographic pair order; a search output counts as C exactly when it is the N-bit characteristic list of C; a distinguisher accepts (value 1) exactly when it outputs [1], every other output being the value −1; reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Theorem 8.1, pp.31–32 (PDF pp.33–34)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Theorem 8.1, pp.31–32 (PDF pp.33–34).
For all rationals `0 < q < p ≤ 1` and every infinite `𝒩 ⊆ ℕ`, the eight assertions (WS), (SS), (WD),
(SD), (W̃S), (S̃S), (W̃D), (S̃D) are equivalent, and for every ordered pair there is a reduction: it
preserves `(p, q)`, `N` and `𝒩`, runs in polynomial time, makes `poly(N)` oracle queries on `N`-vertex
graphs, and does not check membership in `𝒩`.

**Formalization Note.** Advantage is in §4's normalization (the threshold is `2 − e^{−N^ξ}`). The
machine is `PDSEquiv.Machine`: a randomized log-cost oracle RAM, polynomial time being worst case on
every branch, for every `N` and graph, bounded by `(N + 2)^c`. The closing sentence of the theorem is
`Reduces`: the reduction, its exponent and its threshold are chosen before the oracle, and no `𝒩`
occurs in it. The acceptance probability of a program is the mass of the output `[1]`, and its
recovery probability the mass of the characteristic list of the planted set. -/
theorem theorem_8_1 (p q : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (𝒩 : Set ℕ) (h𝒩 : 𝒩.Infinite) :
    List.TFAE (theEight.map fun A => Holds A p q 𝒩) ∧
      ∀ X ∈ theEight, ∀ Y ∈ theEight, Reduces p q X Y := by sorry

end PDSEquiv
