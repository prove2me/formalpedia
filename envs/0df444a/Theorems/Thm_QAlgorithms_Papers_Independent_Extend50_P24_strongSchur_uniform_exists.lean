-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P24_strongSchur_uniform_exists
-- name    : QAlgorithms.Papers.Independent.Extend50.P24.strongSchur_uniform_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:45:04.404425+00:00
-- url     : https://prove2.me/theorems/6ffd7ec7-3b8c-421b-b5e9-af283876fd60
-- title:
--   Uniform efficient high-dimensional strong Schur transform
-- statement:
--   Let $n,d\geq1$ be integers. Give $(\mathbb C^d)^{\otimes n}$ its fixed alphabet and numbered tensor factors. There is a choice, fixed once for every $n,d$, of an exact unitary Schur transform $S_{n,d}$. It simultaneously intertwines tensor permutations and the diagonal $U(d)$ action with the corresponding irreducible factors. Its symmetric factor is in the Young orthonormal basis with the signed coefficients (2.5)–(2.8). Its unitary factor is in a physical Gelfand–Tsetlin basis: at every $1\leq k\leq d$, each basis vector lies in the actual polynomial $U(k)$ factor specified by the subtableau with alphabet entries at most $k$.
--
--   There is a single classical polynomial-time circuit constructor, a fixed finite universal gate set, and a polynomial $p$ independent of $n,d$, the precision, and the input state. On a positive integer request $t$ the constructor produces a circuit $C_{n,d,t}$ satisfying
--
--   $$
--   \operatorname{work}(C_{n,d,t})\leq p(1+n+\lceil\log_2d\rceil+t),\qquad
--   \|C_{n,d,t}E_{\mathrm{in}}v-E_{\mathrm{out}}S_{n,d}v\|_2\leq 2^{-t}\|v\|_2
--   \quad\text{for every }v.
--   $$
--
--   Here $E_{\mathrm{in}}$ and $E_{\mathrm{out}}$ are fixed injective binary basis encodings with clean ancillary coordinates. Work counts every executed gate and the allocated and serialized circuit description; generation is performed by a polynomial-time Turing machine. Thus $t=\lceil\log_2(1/\epsilon)\rceil$ gives operator-norm accuracy $\epsilon$ for every $0<\epsilon<1$, with polynomial dependence on $n,\log d,\log(1/\epsilon)$.
--
--   This is the paper's circuit-existence claim, kept separate from correctness of its particular DualSchur pseudocode. **Formalization Note.** Alphabet and tableau entries are zero-based. Physical tower adaptation is stated through isometric intertwiners into the accepted polynomial Schur modules, not merely through GT labels.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, PDF p. 2, Abstract and §1 main existence result: efficient high-dimensional strong Schur transform

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- Abstract and §1, PDF pp.1-2, with strong-basis meaning from p.16:
a uniform efficient high-dimensional strong Schur transform exists.
The exact simultaneous Young/physical-GT frame is fixed once per positive
n,d, before every t and input. This does not assert correctness of the
particular DualSchur pseudocode. The additive 1 preserves d=1. -/
theorem strongSchur_uniform_exists :
    ∃ frames : (n d : ℕ) → 0 < n → 0 < d → StrongSchurFrame n d,
    ∃ circuits : ℕ → ℕ → ℕ → CompiledCircuit,
    ∃ p : Polynomial ℕ, ∃ generate : List Bool → List Bool,
      QAlgorithms.Complexity.PolyTimeComputable generate ∧
      ∀ n d t (hn : 0 < n) (hd : 0 < d), 0 < t →
        generate (requestCode n d t) = (circuits n d t).code ∧
        (circuits n d t).work ≤ p.eval (1 + n + Nat.clog 2 d + t) ∧
        Approximates tensorWordCode strongCode (strongMatrix (frames n d hn hd))
          (circuits n d t) ((2 : ℝ) ^ (-(t : ℤ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P24

end
