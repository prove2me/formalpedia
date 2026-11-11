-- Prove2me | Theorems.Thm_QuadStatRE_Main_theorem_1_2
-- name    : QuadStatRE.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:45:28.646802+00:00
-- url     : https://prove2.me/theorems/fb9949e1-20ee-4eae-916b-640382e50d1d
-- title:
--   Theorem 1.2 — every finite function has a degree-2, 3-local randomized encoding with errors at most 2^{−λ}, in polynomial time for ⊕L/poly
-- statement:
--   **(i) Every finite function.** For all $n,\ell\in\mathbb N$, every $f:\{0,1\}^n\to\{0,1\}^\ell$ and every security parameter $\lambda\in\mathbb N$ there are $\rho,m,\tau\in\mathbb N$, an encoder $\hat f_\lambda:\{0,1\}^n\times\{0,1\}^\rho\to\{0,1\}^m$ given by a polynomial description over $\mathbb F_2$, a deterministic decoder $\mathrm{Dec}$ and a simulator $\mathrm{Sim}:\{0,1\}^\ell\times\{0,1\}^\tau\to\{0,1\}^m$ such that every output bit of $\hat f_\lambda(v;r)$ is a polynomial of total degree at most $2$ in $(v,r)$ jointly and depends on at most $3$ bits of $(v,r)$, and for every input $v$
--   $$\Pr_r\big[\mathrm{Dec}(\hat f_\lambda(v;r))\ne f(v)\big]\le2^{-\lambda},\qquad\mathrm{SD}\big(\hat f_\lambda(v;U_\rho),\ \mathrm{Sim}(f(v);U_\tau)\big)\le2^{-\lambda}.$$
--
--   **(ii) Efficient for $\oplus\mathsf L/\mathsf{poly}$.** For every function family $\{f_n\}$ in $\oplus\mathsf L/\mathsf{poly}$ (each output bit of $f_n$ a mod-2 branching program, the programs generated from $1^n$ in polynomial time) there is one construction which, for every $(n,\lambda)$, provides an encoding of $f_n$ with all the properties of (i), and whose construction, encoder, decoder and simulator are computed by fixed machines in time polynomial in $n$ and $\lambda$ (on the unary input $1^n0\,1^\lambda0$).
--
--   The theorem settles the question, open since [IK00], whether degree-2 randomized encodings are universal when small statistical errors are allowed; with degree 2 and locality 3 both minimal.
--
--   **Formalization Note.** Encoders are published `QuadraticRE.Desc` descriptions (lists of monomials) with `DegLE 2`; locality is the semantic `LocalLE D 3`; the decoder returns `Option`, with $\bot$ counted as an error; the simulator is a deterministic map of $f(v)$ and uniform coins, never an arbitrary law and never seeing $v$ or $r$. Polynomial time is the published `Construction.IsPolyTime`: four fixed Turing machines (Mathlib's `TM2ComputableInPolyTime`) for the construction (description and coin count), the encoder, the decoder and the simulator, each with input prefixed by the encoding of $(n,\lambda)$.
--
--   Differences from the source:
--
--   - reading: if f = {f_n} is a function family in NC^1 (or, more generally, in NL/poly or ⊕L/poly) → every family of mod-2 branching programs generated from 1^n by a polynomial-time machine; reason: ⊕L/poly is the most general class the page names (NC¹ ⊆ NL/poly ⊆ ⊕L/poly); footnote 1 defines it with polynomial-time generation
--   - encoding: polynomial-size mod-2 branching programs → the published QuadraticRE.BP (no parallel edges), size bounded through polynomial-time generation; reason: subdividing an edge keeps the class unchanged
--   - encoding: degree 2: every output bit a multilinear polynomial of total degree ≤ 2 in (v, r) jointly → an explicit description D with D.DegLE 2; reason: the published description and degree notion
--   - encoding: locality 3: every output bit depends on at most 3 bits of (v, r) → LocalLE D 3 (semantic dependence); reason: the page's definition, stated semantically
--   - encoding: deterministic decoder → Dec : (Fin m → F₂) → Option (Fin ℓ → F₂), none counted as a decoding error; reason: the published IsRE convention; equivalent to a total decoder
--   - encoding: randomized simulator → a deterministic map of (f(v), τ uniform coin bits), passed to IsRE as its output law; reason: a randomized algorithm with a uniform tape
--   - encoding: encoder, decoder and simulator implemented in time polynomial in n and λ → Construction.IsPolyTime for the unary encoding 1^n 0 1^λ 0 of (n, λ) (construction, encoder, decoder, simulator machines); reason: uniform polynomial time jointly in n and λ (§2.5)
--   - encoding: errors at most 2^{−λ} for every security parameter λ → (1/2)^λ for every λ : ℕ, on every input; reason: the same bound; λ = 0 included
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 3, Theorem 1.2

import Mathlib
import Definitions.Def_QuadraticRE_Desc
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadraticRE_Rep
import Definitions.Def_QuadraticRE_PolyTimeFn
import Definitions.Def_QuadraticRE_Construction
import Definitions.Def_QuadStatRE_Main_Locality
import Definitions.Def_QuadStatRE_Main_ParityLPoly
open QuadraticRE

namespace QuadStatRE.Main

/-- Theorem 1.2 (Main theorem), p. 3. (i) Every finite function `f : {0,1}^n → {0,1}^ℓ` admits, for
every security parameter `λ ∈ ℕ`, a randomized encoding of degree 2 and locality 3 whose correctness
and privacy errors are at most `2^{−λ}`: an encoder given by a description of total degree at most two
jointly in the input and the random bits, each output bit depending on at most three of those bits, a
deterministic decoder seeing only the encoding, and a simulator seeing only `f(v)` and uniform coins.
(ii) For every `⊕L/poly` family `{f_n}` there is one construction over the parameters `(n, λ)` with the
same properties at every `(n, λ)`, whose construction, encoder, decoder and simulator run in time
polynomial in `n` and `λ`. -/
theorem theorem_1_2 :
    (∀ (n ℓ : ℕ) (f : (Fin n → F2) → (Fin ℓ → F2)) (lam : ℕ),
      ∃ (ρ m τ : ℕ) (D : Desc n ρ m) (Dec : (Fin m → F2) → Option (Fin ℓ → F2))
        (Sim : (Fin ℓ → F2) → (Fin τ → F2) → (Fin m → F2)),
        D.DegLE 2 ∧ LocalLE D 3 ∧
          IsRE f D.eval ((1 / 2 : ℝ) ^ lam) ((1 / 2 : ℝ) ^ lam) Dec (fun y => law (Sim y))) ∧
    (∀ F : ParityLPolyFamily,
      ∃ C : Construction (fun p : NLam => (F.gen p.n).N) (fun p : NLam => (F.gen p.n).b),
        C.IsPolyTime encNLam ∧
          ∀ p : NLam, (C.desc p).DegLE 2 ∧ LocalLE (C.desc p) 3 ∧
            IsRE (F.gen p.n).eval (C.desc p).eval ((1 / 2 : ℝ) ^ p.lam) ((1 / 2 : ℝ) ^ p.lam)
              (C.dec p) (fun y => law (C.sim p y))) := by sorry

end QuadStatRE.Main
