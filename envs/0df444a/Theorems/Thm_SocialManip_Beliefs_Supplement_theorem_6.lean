-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_6
-- name    : SocialManip.Beliefs.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:18:09.592588+00:00
-- url     : https://prove2.me/theorems/4475184b-16fe-4ec9-a385-94516d932c78
-- title:
--   Theorem 6, p. 26 (corrected: strict criterion) — symmetric networks with φk|B|/|D| > (1+b)/(1−b) are impervious; equality fails on a triangle
-- statement:
--   Fix a degree-$k$ symmetric network in the sense of Definition 7 (every agent has $k$ neighbours in the symmetric unweighted network $G^*$, and every DeGroot uses equal-influence weights $\theta_i=\alpha_{ij}=1/(1+k)$ on herself and her neighbours) with a symmetric placement $B$ of $m=|B|$ Bayesians (Definition 8: $G^*$ is undirected and the subgraph induced on the DeGroots $D$ is symmetric). Let $\varphi$ be the fraction of links into Bayesians that come from DeGroots. Under the standing constraints, the game domain and Assumption 1,
--   $$\frac{\varphi k|B|}{|D|}>\frac{1+b}{1-b}\quad\Longrightarrow\quad\text{the network is impervious to manipulation.}$$
--   The boundary case of the printed condition, equality, is excluded and the statement shows that this exclusion is necessary. Take the undirected triangle without self links, agent $0$ Bayesian, $\theta_i=\alpha_{ij}=1/3$ for the DeGroots, $p_i=3/4$, $q=1/10$, $\lambda=1$, $\lambda^*=100$, $\varepsilon=1/4$, $b=0$. All standing assumptions and both symmetry conditions hold, and
--   $$\frac{\varphi k|B|}{|D|}=1=\frac{1+b}{1-b},\qquad\text{yet the network is susceptible}.$$
--   Theorem 6 gives a simple sufficient condition for imperviousness in symmetric networks, in terms of the degree $k$ and the ratio of Bayesians to DeGroots.
--
--   **Formalization Note** The proof on p. 52 computes the common false-state centrality under maximal interference, $D(1_D)=|D|/(\varphi k|B|+|D|)$, and then treats $D(1_D)=(1-b)/2$ as "no manipulation". At equality the limiting belief sits exactly on the action threshold, and finite-horizon beliefs can approach it from above. In the triangle the initial belief in $R$ is $9/10$, and with probability greater than $0.99$ both DeGroots stay strictly above $1/2$ at every integer horizon (DISPROOF.md gives the recurrence and an exponential-moment bound). With strict inequality, $D(\gamma)\le D(1_D)<(1-b)/2$ for every intervention. The ratio uses the printed $m$; the proof's $\varphi kn$ is a slip. When there are no DeGroots or no Bayesians, the source ratio is undefined, and the Lean ratio (division by zero gives $0$) never satisfies the strict hypothesis.
--
--   Differences from the source:
--   - correction: the ≥ sufficient condition → the strict > condition, together with an explicit susceptible symmetric triangle at equality; reason: the p. 52 proof treats a limiting belief equal to the threshold as no manipulation, but finite-horizon beliefs can approach it from above; the strict condition makes every limiting false-state belief strictly smaller than (1−b)/2
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 6, p. 26; symmetric graphs and Definition 7 p. 25; Definition 8 and φ p. 26; (3) p. 23; proof p. 52

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- Theorem 6 with the boundary corrected, and the equality case refuted.
(1) Every degree-`k` symmetric network with a symmetric placement of Bayesians whose ratio
`φk|B|/|D|` strictly exceeds `(1+b)/(1-b)` is impervious (the p. 52 proof shows that the maximal
false-state centrality `D(1_D) = |D|/(φk|B| + |D|)` is then strictly below the action
threshold `(1-b)/2`).
(2) Equality does not suffice: in this symmetric triangle the prior R-belief is 9/10 and rapid
misinformation leaves positive probability of approaching the threshold 1/2 from above. -/
theorem theorem_6 :
    (∀ {n : ℕ} (M : Model n) (adj : Fin n → Fin n → Prop) (k : ℕ),
      M.Standing → M.GameDomain → M.Assumption1 adj →
      IsDegreeSymmetric M.B M.θ M.α adj k → IsSymmetricPlacement M.B adj →
      (1 + M.b) / (1 - M.b) <
        bayesEdgeFraction M.B adj * k * M.B.card / ((n : ℝ) - M.B.card) →
      Impervious M) ∧
    (let M : Model 3 :=
      { B := {0}
        θ := fun _ => 1 / 3
        α := Matrix.of fun i j => if i ≠ j then 1 / 3 else 0
        p := fun _ => 3 / 4
        q := 1 / 10
        lam := 1
        lamStar := 100
        ε := 1 / 4
        b := 0 }
    let adj : Fin 3 → Fin 3 → Prop := fun i j => i ≠ j
    M.Standing ∧ M.GameDomain ∧ M.Assumption1 adj ∧
      IsDegreeSymmetric M.B M.θ M.α adj 2 ∧ IsSymmetricPlacement M.B adj ∧
      bayesEdgeFraction M.B adj * 2 * M.B.card / ((3 : ℝ) - M.B.card) =
        (1 + M.b) / (1 - M.b) ∧ ¬ Impervious M) := by sorry

end SocialManip.Beliefs.Supplement
