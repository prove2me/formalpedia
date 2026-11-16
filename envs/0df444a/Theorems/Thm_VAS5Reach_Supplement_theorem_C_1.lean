-- Prove2me | Theorems.Thm_VAS5Reach_Supplement_theorem_C_1
-- name    : VAS5Reach.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:51:54.579532+00:00
-- url     : https://prove2.me/theorems/d3fd065a-83f3-4c9b-9019-ec53d9ec4bbe
-- title:
--   Theorem C.1 (formal Theorem 1.3) — polynomial factorization of the reachability relation of every $d$-VAS, $d\ge3$
-- statement:
--   For every fixed dimension $d\ge3$ there is a polynomial $P_d$ such that every $d$-VAS $V$ admits a finite family $\mathcal F$ of sequences of relations $(R_1,\dots,R_m)$ with the following properties.
--
--   1. $\displaystyle \mathrm{Reach}_V=\bigcup_{(R_1,\dots,R_m)\in\mathcal F}R_1\circ\cdots\circ R_m .$
--   2. Every sequence in $\mathcal F$ has $1\le m\le P_d(\mathrm{SIZE}(V))$.
--   3. Each factor is $R_i=\mathrm{Reach}_{V_i}\subseteq\mathrm{Reach}_V$, where $V_i$ is either $[\![V]\!]_{I,B}$ for some $I\subseteq[d]$ with $|I|=3$ and $B\le P_d(\mathrm{SIZE}(V))$, or a mixed LPS $\Lambda$ with $\|\Lambda\|,|\Lambda|\le P_d(\mathrm{SIZE}(V))$.
--   4. For every factor $R_i$ and every $(x,y)\in R_i$, $\ell_V(x,y)\le\ell_{V_i}(x,y)$.
--
--   Here $\mathrm{SIZE}(V)=1+d|T|(\|T\|+1)+2$ and $\ell$ denotes the least length of a run or witness. This is the formal version of Theorem 1.3: the reachability relation of every $d$-VAS, $d\ge3$, admits a polynomial factorization. It gives semilinearity of 5-VAS reachability relations (Corollary 1.4) and the $\mathbf F_d$ bound of Theorem 1.5.
--
--   Differences from the source:
--   - encoding: a finite family F of sequences of relations (R₁, …, R_m), each Rᵢ = Reach_{Vᵢ} → F : List (List (Factor (Fin d))), each factor an encoding [[V]]_{I,B} or a mixed LPS, and Rᵢ = Factor.Rel T fᵢ; reason: a finite family is a list; the page requires each Rᵢ to be the reachability relation of a Vᵢ of one of the two forms, so giving Vᵢ is the same as giving Rᵢ
--   - encoding: Reach_{[[V]]_{I,B}} (viewed on configurations of V by restoring the counter values stored in the states, p.20) → pairs (x, y) of ℕ^d with x↾I, y↾I ∈ [0, B]^I and a run ((), x↾I)(x↾[d]∖I) −π→ ((), y↾I)(y↾[d]∖I) in the published encode (VASS.ofVAS T) I B; its length is the witness length; reason: this is the identification the paper fixes on p.20; the box conditions are those under which [[x]]_{I,B} is defined (p.16)
--   - encoding: ℓ_V(x, y) ≤ ℓ_{Vᵢ}(x, y) for (x, y) ∈ Rᵢ (minimum lengths, ∞ if none) → for every n, a witness of Vᵢ from x to y of length n yields a run of V from x to y of length ≤ n; reason: equivalent to comparing the minima (ℓ_{Vᵢ}(x, y) is attained by a witness); no infimum over ℕ, whose value on ∅ would be 0, is formed
--   - encoding: a polynomial P_d → P : Polynomial ℕ, chosen after d and before V; reason: only upper bounds are asserted, and every integer polynomial is dominated on ℕ by the polynomial with the absolute values of its coefficients
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem C.1, p.47 (PDF p.49), the formal version of Theorem 1.3, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_Supplement_Factor

namespace VAS5Reach.Supplement

open VAS5Reach

/-- **Theorem C.1** (formal version of Theorem 1.3). For every fixed dimension `d ≥ 3`, there
exists a polynomial `P_d` such that every `d`-VAS `V` admits a finite family `F` of sequences of
relations `(R₁, …, R_m)` satisfying the following properties:
`Reach_V = ⋃_{(R₁,…,R_m) ∈ F} R₁ ◦ ⋯ ◦ R_m`. Every sequence in `F` has `1 ≤ m ≤ P_d(SIZE(V))`.
Each factor is `Rᵢ = Reach_{Vᵢ} ⊆ Reach_V`, where `Vᵢ` has one of the following forms:
1. `Vᵢ = [[V]]_{I,B}` for some `I ⊆ [d]` with `|I| = 3` and `B ≤ P_d(SIZE(V))`;
2. `Vᵢ = Λ` for some mixed LPS `Λ`, with `∥Λ∥, |Λ| ≤ P_d(SIZE(V))`.
Moreover, for every factor `Rᵢ` and every `(x, y) ∈ Rᵢ`, `ℓ_V(x, y) ≤ ℓ_{Vᵢ}(x, y)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem C.1, printed p. 47
(PDF p. 49), "the formal version of Theorem 1.3" (Theorem 1.3: printed p. 2, PDF p. 4).

**Formalization Note** `F` is a list of lists of factors (`Factor`: an encoding `[[V]]_{I,B}` or
a mixed LPS), `Rᵢ = Factor.Rel T fᵢ`, composition is left to right (`relComp`). `SIZE(V)` is the
published `vasSizeV T`; `P_d` is a polynomial with natural coefficients, chosen before `V`. The
distance inequality `ℓ_V(x, y) ≤ ℓ_{Vᵢ}(x, y)` is stated as: every witness of `Vᵢ` from `x` to `y`
of length `n` yields a run of `V` from `x` to `y` of length `≤ n` (no minimum over `ℕ` is
formed). -/
theorem theorem_C_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : Polynomial ℕ, ∀ T : Finset (Fin d → ℤ),
      ∃ F : List (List (Factor (Fin d))),
        (∀ x y : Fin d → ℕ,
          VASReach T x y ↔ ∃ seq ∈ F, relComp (seq.map (Factor.Rel T)) x y) ∧
        ∀ seq ∈ F, 1 ≤ seq.length ∧ seq.length ≤ P.eval (vasSizeV T) ∧
          ∀ f ∈ seq, f.Bounded (P.eval (vasSizeV T)) ∧
            (∀ x y, Factor.Rel T f x y → VASReach T x y) ∧
            (∀ x y n, Factor.HasWitness T f x y n →
              ∃ w, IsVASRun T x w y ∧ w.length ≤ n) := by sorry

end VAS5Reach.Supplement
