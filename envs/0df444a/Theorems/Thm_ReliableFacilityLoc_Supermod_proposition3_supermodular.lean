-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_proposition3_supermodular
-- name    : ReliableFacilityLoc.Supermod.proposition3_supermodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:27.351346+00:00
-- url     : https://prove2.me/theorems/7f1a308b-511b-4ddb-9ba8-afb51f80a4d2
-- title:
--   Proposition 3: $\Phi_i$ is supermodular on sets of size at most $R$, in the form (18)
-- statement:
--   Consider the reliable facility location model with customers $i = 0, \dots, I-1$, regular facilities $j = 0, \dots, J-1$, demand rates $\lambda_i \ge 0$, unit costs $d_{ij}$, penalties $\varphi_i$, failure probabilities $0 \le q_j < 1$, Lagrange multipliers $\mu_{ij}$, and $R \ge 1$ backup levels, and let $\Phi_i(S)$ be the minimum cost of serving customer $i$ using only facilities of $S$.
--
--   For every customer $i$, every set $S$ of regular facilities, and all regular facilities $u \ne v$ not in $S$ with $|S| + 2 \le R$,
--
--   $$
--   \Phi_i(S\cup\{u,v\}) - \Phi_i(S\cup\{u\}) \ \ge\ \Phi_i(S\cup\{v\}) - \Phi_i(S).
--   $$
--
--   That is, the marginal cost of adding a facility increases as the set grows, so $\Phi_i$ is supermodular on the sets that the customer's assignment problem (MSF$_i$) ranges over. This is the property that lets (MSF$_i$) be solved by the branch-and-bound algorithm of Goldengorin et al. for supermodular minimization.
--
--   **Formalization Note** The paper states "$\Phi_i$ is supermodular" without restriction; the hypothesis $|S \cup \{u,v\}| \le R$ is added because the unrestricted statement is false. For $J = 5$, $R = 3$, $\lambda_i = 1$, $\mu \equiv 0$, $d = (3.747, 4.39, 5.084, 7.784, 5.209)$, $q = (0.393, 0.733, 0.043, 0, 0)$, $\varphi_i = 11.558$, $S = \{0,2,3\}$, $u = 1$, $v = 4$, the left side is about $-0.04418$ and the right side about $-0.04351$. The paper's proof uses the closed form of $\Phi_i$, valid only for $|S| \le R$, and (MSF$_i$) evaluates $\Phi_i$ only on such sets. Costs, penalties and multipliers are arbitrary reals.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 13 (PDF 15), Proposition 3; proof in Appendix A.3, pp. 35–37 (PDF 37–39), inequality (18)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Proposition 3** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010), p. 13, PDF 15; proof in
Appendix A.3, pp. 35–37, PDF 37–39), in the form (18) its proof establishes. For every customer
`i`, every set `S` of regular facilities and all regular facilities `u ≠ v` outside `S` with
`|S| + 2 ≤ R`,
`Φ_i(S ∪ {u, v}) − Φ_i(S ∪ {u}) ≥ Φ_i(S ∪ {v}) − Φ_i(S)`.

Printed (p. 13): "Proposition 3. The set function Φi is supermodular, for all i = 0, ··· , I − 1."
Printed (p. 35): "Let S ⊆ {0, ··· , J − 1} be a subset of candidate locations, and
u, v ∈ {0, ··· , J − 1} \ S, we show that Φi(S ∪ {u, v}) − Φi(S ∪ {u}) ≥ Φi(S ∪ {v}) − Φi(S). (18)"

Formalization Note: the hypothesis `|S| + 2 ≤ R`, i.e. `|S ∪ {u, v}| ≤ R`, is added. Without it the
statement is false: for `J = 5`, `R = 3`, `λ_i = 1`, `µ ≡ 0`, `d = (3.747, 4.39, 5.084, 7.784, 5.209)`,
`q = (0.393, 0.733, 0.043, 0, 0)`, `φ_i = 11.558`, `S = {0, 2, 3}`, `u = 1`, `v = 4`, the left side
is ≈ −0.04418 and the right side ≈ −0.04351. The proof uses the closed form of `Φ_i`, which holds
only for `|S| ≤ R`, and (MSF_i) only evaluates `Φ_i` on sets with `|S| ≤ R` (constraint (6c),
p. 13). `0 ≤ λ_i` (demand rates; the proof multiplies a nonpositive bracket by `λ_i q_u`),
`0 ≤ q_j < 1` and `R ≥ 1` are the standing assumptions of §3.1 (pp. 7–8). The costs `d`, penalties
`φ` and multipliers `µ` are arbitrary reals. -/
theorem proposition3_supermodular {I J R : ℕ} (lam : Fin I → ℝ) (d : Fin I → Fin J → ℝ)
    (phi : Fin I → ℝ) (q : Fin J → ℝ) (mu : Fin I → Fin J → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R) (i : Fin I) (S : Finset (Fin J))
    (u v : Fin J) (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S) (hS : S.card + 2 ≤ R) :
    Phi (lam i) (d i) (phi i) q (mu i) R (insert u (insert v S)) -
        Phi (lam i) (d i) (phi i) q (mu i) R (insert u S) ≥
      Phi (lam i) (d i) (phi i) q (mu i) R (insert v S) -
        Phi (lam i) (d i) (phi i) q (mu i) R S := by sorry

end ReliableFacilityLoc.Supermod
