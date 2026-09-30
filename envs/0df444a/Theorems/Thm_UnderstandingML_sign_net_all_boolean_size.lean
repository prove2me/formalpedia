-- Prove2me | Theorems.Thm_UnderstandingML_sign_net_all_boolean_size
-- name    : UnderstandingML.sign_net_all_boolean_size
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:00:28.417088+00:00
-- url     : https://prove2.me/theorems/ff333858-bf94-409b-8406-a275e23dab7d
-- title:
--   Theorem 20.2: a sign network whose class contains all functions {0,1}^n → {0,1} has 2^{n/3} ≤ 2|V|, so the minimal size s(n) is exponential in n
-- statement:
--   **Theorem 20.2.** For every $n$, let $s(n)$ be the minimal integer such that there exists a graph $(V, E)$ with $|V| = s(n)$ such that the hypothesis class $H_{V,E,\operatorname{sign}}$ contains all the functions from $\{0,1\}^n$ to $\{0,1\}$. Then, $s(n)$ is exponential in $n$.
--
--   Formally, as the proof gives it ($2^n \le \operatorname{VCdim} \le 2|E|\log_2(16|E|)$ and $|E| \le |V|^2$): every layered graph of depth $\ge 1$ whose sign class contains all functions $\{0,1\}^n \to \{0,1\}$ satisfies $2^{n/3} \le 2|V|$. (The sigmoid case, stated without proof, is not included.)
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.3 p. 272, Theorem 20.2 with its proof

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 20.2** (p. 272). For every `n`, let `s(n)` be the minimal integer such that there
exists a graph `(V, E)` with `|V| = s(n)` such that the hypothesis class `H_{V,E,sign}` contains
all the functions from `{0,1}^n` to `{0,1}`. Then `s(n)` is exponential in `n`.
Explicitly, as the proof gives it (`2^n ≤ VCdim ≤ O(|E| log |E|)` and `|E| ≤ |V|²`): every
such graph has `2^n ≤ 8|V|³`, i.e. `|V| ≥ 2^{n/3}/2`. -/
theorem sign_net_all_boolean_size (n : ℕ) (G : LayeredGraph) (hd : 1 ≤ G.depth)
    (hG : ∀ f : (Fin n → Bool) → Bool, ∃ h ∈ signNetClass n G,
      ∀ x : Fin n → Bool, h (fun i ↦ if x i then (1 : ℝ) else 0) = f x) :
    (2 : ℝ) ^ ((n : ℝ) / 3) ≤ 2 * G.size := by sorry

end UnderstandingML
